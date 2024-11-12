module Lintings where

import AST
import LintTypes


--------------------------------------------------------------------------------
-- AUXILIARES
--------------------------------------------------------------------------------

-- Computa la lista de variables libres de una expresión
freeVariables :: Expr -> [Name]
freeVariables (Var x) = [x]
freeVariables (Lit _ )= []
freeVariables (Infix _ e1 e2) = freeVariables e1 ++ freeVariables e2
freeVariables (App e1 e2) = freeVariables e1 ++ freeVariables e2
freeVariables (Lam x e) = filter (/= x) (freeVariables e)
freeVariables (Case e1 e2 (x, y, e3)) = freeVariables e1 ++ freeVariables e2 ++ filter (/= x) (filter (/= y) (freeVariables e3))
freeVariables (If e1 e2 e3) = freeVariables e1 ++ freeVariables e2 ++ freeVariables e3

--------------------------------------------------------------------------------
-- LINTINGS
--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
-- Computación de constantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Reduce expresiones aritméticas/booleanas
-- Construye sugerencias de la forma (LintCompCst e r)
lintComputeConstantAux :: Expr -> [LintSugg] -> (Expr, [LintSugg])
lintComputeConstantAux (Infix op (Lit (LitInt x)) (Lit (LitInt y))) acc =
    case op of
        Add -> if x + y >= 0
                  then let sugg = Lit (LitInt (x + y))
                       in (sugg, acc ++ [LintCompCst (Infix Add (Lit (LitInt x)) (Lit (LitInt y))) sugg])
                  else (Infix Add (Lit (LitInt x)) (Lit (LitInt y)), acc)
        Sub -> if x - y >= 0
                  then let sugg = Lit (LitInt (x - y))
                       in (sugg, acc ++ [LintCompCst (Infix Sub (Lit (LitInt x)) (Lit (LitInt y))) sugg])
                  else (Infix Sub (Lit (LitInt x)) (Lit (LitInt y)), acc)
        Mult -> if x * y >= 0
                then let sugg = Lit (LitInt (x * y))
                    in (sugg, acc ++ [LintCompCst (Infix Mult (Lit (LitInt x)) (Lit (LitInt y))) sugg])
                else (Infix Mult (Lit (LitInt x)) (Lit (LitInt y)), acc)
        Div -> if y /= 0 && x `div` y >= 0
                  then let sugg = Lit (LitInt (x `div` y))
                       in (sugg, acc ++ [LintCompCst (Infix Div (Lit (LitInt x)) (Lit (LitInt y))) sugg])
                  else (Infix Div (Lit (LitInt x)) (Lit (LitInt y)), acc)
        _ -> (Infix op (Lit (LitInt x)) (Lit (LitInt y)), acc)

lintComputeConstantAux (Infix op (Lit (LitBool x)) (Lit (LitBool y))) acc =
    case op of
        And -> let sugg = Lit (LitBool (x && y))
               in (sugg, acc ++ [LintCompCst (Infix And (Lit (LitBool x)) (Lit (LitBool y))) sugg])
        Or  -> let sugg = Lit (LitBool (x || y))
               in (sugg, acc ++ [LintCompCst (Infix Or (Lit (LitBool x)) (Lit (LitBool y))) sugg])
        _ -> (Infix op (Lit (LitBool x)) (Lit (LitBool y)), acc)

lintComputeConstantAux (Infix op e1 e2) acc =
    let (e1', acc1) = lintComputeConstantAux e1 acc
        (e2', acc2) = lintComputeConstantAux e2 acc1
    in if e1 == e1' && e2 == e2'
       then (Infix op e1 e2, acc2)
       else lintComputeConstantAux (Infix op e1' e2') acc2

lintComputeConstantAux (App e1 e2) acc =
    let (e1', acc1) = lintComputeConstantAux e1 acc
        (e2', acc2) = lintComputeConstantAux e2 acc1
    in (App e1' e2', acc2)

lintComputeConstantAux (Lam x e) acc =
    let (e', acc1) = lintComputeConstantAux e acc
    in (Lam x e', acc1)

lintComputeConstantAux (Case e1 e2 (x, y, e3)) acc =
    let (e1', acc1) = lintComputeConstantAux e1 acc
        (e2', acc2) = lintComputeConstantAux e2 acc1
        (e3', acc3) = lintComputeConstantAux e3 acc2
    in (Case e1' e2' (x, y, e3'), acc3)

lintComputeConstantAux (If e1 e2 e3) acc =
    let (e1', acc1) = lintComputeConstantAux e1 acc
        (e2', acc2) = lintComputeConstantAux e2 acc1
        (e3', acc3) = lintComputeConstantAux e3 acc2
    in (If e1' e2' e3', acc3)

lintComputeConstantAux expr acc = (expr, acc)

lintComputeConstant :: Linting Expr
lintComputeConstant exp = lintComputeConstantAux exp []
                    

--------------------------------------------------------------------------------
-- Eliminación de chequeos redundantes de booleanos
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Elimina chequeos de la forma e == True, True == e, e == False y False == e
-- Construye sugerencias de la forma (LintBool e r)
lintRedBoolAux :: Expr -> [LintSugg] -> (Expr, [LintSugg])
lintRedBoolAux (Infix Eq (Lit (LitBool x)) e) acc =
    let (e', acc1) = lintRedBoolAux e acc
        sugg = if x then e' else (App (Var "not") e')
    in (sugg, acc1 ++ [LintBool (Infix Eq (Lit (LitBool x)) e') sugg])

lintRedBoolAux (Infix Eq e (Lit (LitBool x))) acc =
    let (e', acc1) = lintRedBoolAux e acc
        sugg = if x then e' else (App (Var "not") e')
    in (sugg, acc1 ++ [LintBool (Infix Eq e' (Lit (LitBool x))) sugg])

lintRedBoolAux (Infix Eq e1 e2) acc =
    let (e1', acc1) = lintRedBoolAux e1 acc
        (e2', acc2) = lintRedBoolAux e2 acc1
    in
        if (e1 == e1' && e2 == e2')
        then (Infix Eq e1 e2, acc2)
        else lintRedBoolAux (Infix Eq e1' e2') acc2 

lintRedBoolAux (Infix op e1 e2) acc =
    let (e1', acc1) = lintRedBoolAux e1 acc
        (e2', acc2) = lintRedBoolAux e2 acc1
    in (Infix op e1' e2', acc2)

lintRedBoolAux (App e1 e2) acc =
    let (e1', acc1) = lintRedBoolAux e1 acc
        (e2', acc2) = lintRedBoolAux e2 acc1
    in (App e1' e2', acc2)

lintRedBoolAux (Lam x e) acc =
    let (e', acc1) = lintRedBoolAux e acc
    in (Lam x e', acc1)

lintRedBoolAux (Case e1 e2 (x, y, e3)) acc =
    let (e1', acc1) = lintRedBoolAux e1 acc
        (e2', acc2) = lintRedBoolAux e2 acc1
        (e3', acc3) = lintRedBoolAux e3 acc2
    in (Case e1' e2' (x, y, e3'), acc3)

lintRedBoolAux (If e1 e2 e3) acc =
    let (e1', acc1) = lintRedBoolAux e1 acc
        (e2', acc2) = lintRedBoolAux e2 acc1
        (e3', acc3) = lintRedBoolAux e3 acc2
    in (If e1' e2' e3', acc3)

lintRedBoolAux expr acc = (expr, acc)

lintRedBool :: Linting Expr
lintRedBool exp = lintRedBoolAux exp []


--------------------------------------------------------------------------------
-- Eliminación de if redundantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Sustitución de if con literal en la condición por la rama correspondiente
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfCondAux :: Expr -> [LintSugg] -> (Expr, [LintSugg])
lintRedIfCondAux (If (Lit (LitBool True)) e1 e2) acc =
    let (sugg, acc1) = lintRedIfCondAux e1 acc
    in (sugg, acc1 ++ [LintRedIf (If (Lit (LitBool True)) sugg e2) sugg])

lintRedIfCondAux (If (Lit (LitBool False)) e1 e2) acc =
    let (sugg, acc1) = lintRedIfCondAux e2 acc
    in (sugg, acc1 ++ [LintRedIf (If (Lit (LitBool False)) e1 sugg) sugg])

lintRedIfCondAux (If e1 e2 e3) acc =
    let (e1', acc1) = lintRedIfCondAux e1 acc
        (e2', acc2) = lintRedIfCondAux e2 acc1
        (e3', acc3) = lintRedIfCondAux e3 acc2
    in 
        case e1' of
            Lit (LitBool True) -> (e2', acc3 ++ [LintRedIf (If e1' e2' e3') e2'])
            Lit (LitBool False) -> (e3', acc3 ++ [LintRedIf (If e1' e2' e3') e3'])
            _ -> (If e1 e2' e3', acc3)

lintRedIfCondAux (Infix op e1 e2) acc =
    let (e1', acc1) = lintRedIfCondAux e1 acc
        (e2', acc2) = lintRedIfCondAux e2 acc1
    in (Infix op e1' e2', acc2)

lintRedIfCondAux (App e1 e2) acc =
    let (e1', acc1) = lintRedIfCondAux e1 acc
        (e2', acc2) = lintRedIfCondAux e2 acc1
    in (App e1' e2', acc2)

lintRedIfCondAux (Lam x e) acc =
    let (e', acc1) = lintRedIfCondAux e acc
    in (Lam x e', acc1)

lintRedIfCondAux (Case e1 e2 (x, y, e3)) acc =
    let (e1', acc1) = lintRedIfCondAux e1 acc
        (e2', acc2) = lintRedIfCondAux e2 acc1
        (e3', acc3) = lintRedIfCondAux e3 acc2
    in (Case e1' e2' (x, y, e3'), acc3)

lintRedIfCondAux expr acc = (expr, acc)

lintRedIfCond :: Linting Expr
lintRedIfCond expr = lintRedIfCondAux expr []

--------------------------------------------------------------------------------
-- Sustitución de if por conjunción entre la condición y su rama _then_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfAndAux :: Expr -> [LintSugg] -> (Expr, [LintSugg])
lintRedIfAndAux (If e1 e2 (Lit(LitBool False))) acc =
    let (e1', acc1) = lintRedIfAndAux e1 acc
        (e2', acc2) = lintRedIfAndAux e2 acc1
        sugg = Infix And e1' e2'
    in (sugg, acc2 ++ [LintRedIf (If e1' e2' (Lit(LitBool False))) sugg])

lintRedIfAndAux (If e1 e2 e3) acc =
    let (e1', acc1) = lintRedIfAndAux e1 acc
        (e2', acc2) = lintRedIfAndAux e2 acc1
        (e3', acc3) = lintRedIfAndAux e3 acc2
    in 
        if e3' == Lit (LitBool False)
        then (Infix And e1' e2', acc3 ++ [LintRedIf (If e1' e2' e3') (Infix And e1' e2')])
        else (If e1' e2' e3', acc3)

lintRedIfAndAux (Infix op e1 e2) acc =
    let (e1', acc1) = lintRedIfAndAux e1 acc
        (e2', acc2) = lintRedIfAndAux e2 acc1
    in (Infix op e1' e2', acc2)

lintRedIfAndAux (App e1 e2) acc =
    let (e1', acc1) = lintRedIfAndAux e1 acc
        (e2', acc2) = lintRedIfAndAux e2 acc1
    in (App e1' e2', acc2)

lintRedIfAndAux (Lam x e) acc =
    let (e', acc1) = lintRedIfAndAux e acc
    in (Lam x e', acc1)

lintRedIfAndAux (Case e1 e2 (x, y, e3)) acc =
    let (e1', acc1) = lintRedIfAndAux e1 acc
        (e2', acc2) = lintRedIfAndAux e2 acc1
        (e3', acc3) = lintRedIfAndAux e3 acc2
    in (Case e1' e2' (x, y, e3'), acc3)

lintRedIfAndAux expr acc = (expr, acc)

lintRedIfAnd :: Linting Expr
lintRedIfAnd expr = lintRedIfAndAux expr []

--------------------------------------------------------------------------------
-- Sustitución de if por disyunción entre la condición y su rama _else_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfOrAux :: Expr -> [LintSugg] -> (Expr, [LintSugg])
lintRedIfOrAux (If e1 (Lit(LitBool True)) e3) acc =
    let (e1', acc1) = lintRedIfOrAux e1 acc
        (e3', acc2) = lintRedIfOrAux e3 acc1
        sugg = Infix Or e1' e3'
    in (sugg, acc2 ++ [LintRedIf (If e1' (Lit(LitBool True)) e3') sugg])

lintRedIfOrAux (If e1 e2 e3) acc =
    let (e1', acc1) = lintRedIfOrAux e1 acc
        (e2', acc2) = lintRedIfOrAux e2 acc1
        (e3', acc3) = lintRedIfOrAux e3 acc2
    in 
        if e2' == Lit (LitBool True)
        then (Infix Or e1' e3', acc3 ++ [LintRedIf (If e1' e2' e3') (Infix Or e1' e3')])
        else (If e1' e2' e3', acc3)

lintRedIfOrAux (Infix op e1 e2) acc =
    let (e1', acc1) = lintRedIfOrAux e1 acc
        (e2', acc2) = lintRedIfOrAux e2 acc1
    in (Infix op e1' e2', acc2)

lintRedIfOrAux (App e1 e2) acc =
    let (e1', acc1) = lintRedIfOrAux e1 acc
        (e2', acc2) = lintRedIfOrAux e2 acc1
    in (App e1' e2', acc2)

lintRedIfOrAux (Lam x e) acc =
    let (e', acc1) = lintRedIfOrAux e acc
    in (Lam x e', acc1)

lintRedIfOrAux (Case e1 e2 (x, y, e3)) acc =
    let (e1', acc1) = lintRedIfOrAux e1 acc
        (e2', acc2) = lintRedIfOrAux e2 acc1
        (e3', acc3) = lintRedIfOrAux e3 acc2
    in (Case e1' e2' (x, y, e3'), acc3)
    
lintRedIfOrAux expr acc = (expr, acc)

lintRedIfOr :: Linting Expr
lintRedIfOr expr = lintRedIfOrAux expr []

--------------------------------------------------------------------------------
-- Chequeo de lista vacía
--------------------------------------------------------------------------------
-- Sugiere el uso de null para verificar si una lista es vacía
-- Construye sugerencias de la forma (LintNull e r)
lintNullAux :: Expr -> [LintSugg] -> (Expr, [LintSugg])
lintNullAux (Infix Eq (Lit LitNil) e) acc =
    let (e', acc1) = lintNullAux e acc
        sugg = App (Var "null") e'
    in (sugg, acc1 ++ [LintNull (Infix Eq (Lit LitNil) e') sugg])

lintNullAux (Infix Eq e (Lit LitNil)) acc =
    let (e', acc1) = lintNullAux e acc
        sugg = App (Var "null") e'
    in (sugg, acc1 ++ [LintNull (Infix Eq e' (Lit LitNil)) sugg])

lintNullAux (Infix Eq (App (Var "length") e) (Lit (LitInt 0))) acc =
    let (e', acc1) = lintNullAux e acc
        sugg = App (Var "null") e'
    in (sugg, acc1 ++ [LintNull (Infix Eq (App (Var "length") e') (Lit (LitInt 0))) sugg])

lintNullAux (Infix Eq (Lit (LitInt 0)) (App (Var "length") e)) acc =
    let (e', acc1) = lintNullAux e acc
        sugg = App (Var "null") e'
    in (sugg, acc1 ++ [LintNull (Infix Eq (Lit (LitInt 0)) (App (Var "length") e')) sugg])

lintNullAux (Infix op e1 e2) acc =
    let (e1', acc1) = lintNullAux e1 acc
        (e2', acc2) = lintNullAux e2 acc1
    in (Infix op e1' e2', acc2)

lintNullAux (App e1 e2) acc =
    let (e1', acc1) = lintNullAux e1 acc
        (e2', acc2) = lintNullAux e2 acc1
    in (App e1' e2', acc2)

lintNullAux (Lam x e) acc =
    let (e', acc1) = lintNullAux e acc
    in (Lam x e', acc1)

lintNullAux (Case e1 e2 (x, y, e3)) acc =
    let (e1', acc1) = lintNullAux e1 acc
        (e2', acc2) = lintNullAux e2 acc1
        (e3', acc3) = lintNullAux e3 acc2
    in (Case e1' e2' (x, y, e3'), acc3)

lintNullAux (If e1 e2 e3) acc =
    let (e1', acc1) = lintNullAux e1 acc
        (e2', acc2) = lintNullAux e2 acc1
        (e3', acc3) = lintNullAux e3 acc2
    in (If e1' e2' e3', acc3)

lintNullAux expr acc = (expr, acc)

lintNull :: Linting Expr
lintNull expr = lintNullAux expr []

--------------------------------------------------------------------------------
-- Eliminación de la concatenación
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (e:[] ++ es), reemplazando por (e:es)
-- Construye sugerencias de la forma (LintAppend e r)

lintAppend :: Linting Expr
lintAppend = undefined

--------------------------------------------------------------------------------
-- Composición
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (f (g t)), reemplazando por (f . g) t
-- Construye sugerencias de la forma (LintComp e r)

lintComp :: Linting Expr
lintComp = undefined


--------------------------------------------------------------------------------
-- Eta Redución
--------------------------------------------------------------------------------
-- se aplica en casos de la forma \x -> e x, reemplazando por e
-- Construye sugerencias de la forma (LintEta e r)

lintEta :: Linting Expr
lintEta = undefined


--------------------------------------------------------------------------------
-- Eliminación de recursión con map
--------------------------------------------------------------------------------

-- Sustituye recursión sobre listas por `map`
-- Construye sugerencias de la forma (LintMap f r)
lintMap :: Linting FunDef
lintMap = undefined


--------------------------------------------------------------------------------
-- Combinación de Lintings
--------------------------------------------------------------------------------


-- Dada una transformación a nivel de expresión, se construye
-- una transformación a nivel de función
liftToFunc :: Linting Expr -> Linting FunDef
liftToFunc = undefined

-- encadenar transformaciones:
(>==>) :: Linting a -> Linting a -> Linting a
lint1 >==> lint2 = undefined

-- aplica las transformaciones 'lints' repetidas veces y de forma incremental,
-- hasta que ya no generen más cambios en 'func'
lintRec :: Linting a -> Linting a
lintRec lints func = undefined
