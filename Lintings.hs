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
    let sugg = if x then e else (App (Var "not") e)
    in (sugg, acc ++ [LintBool (Infix Eq (Lit (LitBool x)) e) sugg])

lintRedBoolAux (Infix Eq e (Lit (LitBool x))) acc =
    let sugg = if x then e else (App (Var "not") e)
    in (sugg, acc ++ [LintBool (Infix Eq e (Lit (LitBool x))) sugg])

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
        if e1 == e1'
        then (If e1 e2' e3', acc3)
        else lintRedIfCondAux (If e1' e2' e3') acc3

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
lintRedIfAnd :: Linting Expr
lintRedIfAnd = undefined

--------------------------------------------------------------------------------
-- Sustitución de if por disyunción entre la condición y su rama _else_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfOr :: Linting Expr
lintRedIfOr = undefined

--------------------------------------------------------------------------------
-- Chequeo de lista vacía
--------------------------------------------------------------------------------
-- Sugiere el uso de null para verificar si una lista es vacía
-- Construye sugerencias de la forma (LintNull e r)

lintNull :: Linting Expr
lintNull = undefined

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
