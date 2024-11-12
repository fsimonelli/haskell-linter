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
lintComputeConstantAux (Infix op e1 e2) acc =
    let (e1', acc1) = lintComputeConstantAux e1 acc
        (e2', acc2) = lintComputeConstantAux e2 acc1
    in case op of
        Add -> case e1' of
            Lit (LitInt x) -> case e2' of
                Lit (LitInt y) -> if x + y >= 0
                                    then let sugg = Lit (LitInt (x + y))
                                         in (sugg, acc2 ++ [LintCompCst (Infix Add e1' e2') sugg])
                                    else (Infix Add e1' e2', acc2)
                _ -> (Infix Add e1' e2', acc2)
            _ -> (Infix Add e1' e2', acc2)
        Sub -> case e1' of
            Lit (LitInt x) -> case e2' of
                Lit (LitInt y) -> if x - y >= 0
                                    then let sugg = Lit (LitInt (x - y))
                                         in (sugg, acc2 ++ [LintCompCst (Infix Sub e1' e2') sugg])
                                    else (Infix Sub e1' e2', acc2)
                _ -> (Infix Sub e1' e2', acc2)
            _ -> (Infix Sub e1' e2', acc2)
        Mult -> case e1' of
            Lit (LitInt x) -> case e2' of
                Lit (LitInt y) -> if x * y >= 0
                                    then let sugg = Lit (LitInt (x * y))
                                         in (sugg, acc2 ++ [LintCompCst (Infix Mult e1' e2') sugg])
                                    else (Infix Mult e1' e2', acc2)
                _ -> (Infix Mult e1' e2', acc2)
            _ -> (Infix Mult e1' e2', acc2)
        Div -> case e1' of
            Lit (LitInt x) -> case e2' of
                Lit (LitInt y) -> if y /= 0 && x `div` y >= 0
                                    then let sugg = Lit (LitInt (x `div` y))
                                         in (sugg, acc2 ++ [LintCompCst (Infix Div e1' e2') sugg])
                                    else (Infix Div e1' e2', acc2)
                _ -> (Infix Div e1' e2', acc2)
        And -> case e1' of
            Lit (LitBool x) -> case e2' of
                Lit (LitBool y) -> let sugg = Lit (LitBool (x && y))
                                   in (sugg, acc2 ++ [LintCompCst (Infix And e1' e2') sugg])
                _ -> (Infix And e1' e2', acc2)
            _ -> (Infix And e1' e2', acc2)
        Or -> case e1' of
            Lit (LitBool x) -> case e2' of
                Lit (LitBool y) -> let sugg = Lit (LitBool (x || y))
                                   in (sugg, acc2 ++ [LintCompCst (Infix Or e1' e2') sugg])
                _ -> (Infix Or e1' e2', acc2)
            _ -> (Infix Or e1' e2', acc2)
        _ -> (Infix op e1' e2', acc2)
        

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
lintRedBoolAux (Infix op e1 e2) acc =
    let (e1', acc1) = lintRedBoolAux e1 acc
        (e2', acc2) = lintRedBoolAux e2 acc1
    in 
        case op of
            Eq -> case e1 of
                Lit(LitBool True) -> (e2', acc2 ++ [LintBool (Infix Eq e1' e2') e2'])
                Lit(LitBool False) -> (App (Var "not") e2', acc2 ++ [LintBool (Infix Eq e1' e2') (App (Var "not") e2')])
                _ -> case e2 of
                    Lit(LitBool True) -> (e1', acc2 ++ [LintBool (Infix Eq e1' e2') e1'])
                    Lit(LitBool False) -> (App (Var "not") e1', acc2 ++ [LintBool (Infix Eq e1' e2') (App (Var "not") e1')])
                    _ -> (Infix op e1' e2', acc2)
            _ -> (Infix op e1' e2', acc2)

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
lintNullAux (Infix op e1 e2) acc =
    let (e1', acc1) = lintNullAux e1 acc
        (e2', acc2) = lintNullAux e2 acc1
    in case op of
        Eq -> case e1' of
            Lit LitNil -> (App (Var "null") e2', acc2 ++ [LintNull (Infix Eq e1' e2') (App (Var "null") e2')])
            App (Var "length") e -> (App (Var "null") e, acc2 ++ [LintNull (Infix Eq e1' e2') (App (Var "null") e)])
            _ -> case e2' of
                Lit LitNil -> (App (Var "null") e1', acc2 ++ [LintNull (Infix Eq e1' e2') (App (Var "null") e1')])
                App (Var "length") e -> (App (Var "null") e, acc2 ++ [LintNull (Infix Eq e1' e2') (App (Var "null") e)])
                _ ->(Infix op e1' e2', acc2)
        _ ->(Infix op e1' e2', acc2)

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

lintAppendAux :: Expr -> [LintSugg] -> (Expr, [LintSugg])
lintAppendAux (Infix Append e1 e2) acc =
    let (e1', acc1) = lintAppendAux e1 acc
        (e2', acc2) = lintAppendAux e2 acc1
    in 
        case e1' of
            Infix Cons e (Lit LitNil) -> (Infix Cons e e2', 
                                           acc2 ++ [LintAppend (Infix Append (Infix Cons e (Lit LitNil)) e2') (Infix Cons e e2')])
            _ -> (Infix Append e1' e2', acc2)

lintAppendAux (Infix op e1 e2) acc =
    let (e1', acc1) = lintAppendAux e1 acc
        (e2', acc2) = lintAppendAux e2 acc1
    in (Infix op e1' e2', acc2)

lintAppendAux (App e1 e2) acc =
    let (e1', acc1) = lintAppendAux e1 acc
        (e2', acc2) = lintAppendAux e2 acc1
    in (App e1' e2', acc2)

lintAppendAux (Lam x e) acc =
    let (e', acc1) = lintAppendAux e acc
    in (Lam x e', acc1)

lintAppendAux (Case e1 e2 (x, y, e3)) acc =
    let (e1', acc1) = lintAppendAux e1 acc
        (e2', acc2) = lintAppendAux e2 acc1
        (e3', acc3) = lintAppendAux e3 acc2
    in (Case e1' e2' (x, y, e3'), acc3)

lintAppendAux (If e1 e2 e3) acc =
    let (e1', acc1) = lintAppendAux e1 acc
        (e2', acc2) = lintAppendAux e2 acc1
        (e3', acc3) = lintAppendAux e3 acc2
    in (If e1' e2' e3', acc3)

lintAppendAux expr acc = (expr, acc)

lintAppend :: Linting Expr
lintAppend expr = lintAppendAux expr []

--------------------------------------------------------------------------------
-- Composición
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (f (g t)), reemplazando por (f . g) t
-- Construye sugerencias de la forma (LintComp e r)
lintCompAux :: Expr -> [LintSugg] -> (Expr, [LintSugg])
lintCompAux (App e1 e2) acc =
    let (e1', acc1) = lintCompAux e1 acc
        (e2', acc2) = lintCompAux e2 acc1
    in 
        case e2' of
            App e3 e4 -> (App (Infix Comp e1' e3) e4 , acc2 ++ [LintComp (App e1' e2') (App (Infix Comp e1' e3) e4)])
            _ -> (App e1' e2', acc2)

lintCompAux (Infix op e1 e2) acc =
    let (e1', acc1) = lintCompAux e1 acc
        (e2', acc2) = lintCompAux e2 acc1
    in (Infix op e1' e2', acc2)

lintCompAux (Lam x e) acc =
    let (e', acc1) = lintCompAux e acc
    in (Lam x e', acc1)

lintCompAux (Case e1 e2 (x, y, e3)) acc =
    let (e1', acc1) = lintCompAux e1 acc
        (e2', acc2) = lintCompAux e2 acc1
        (e3', acc3) = lintCompAux e3 acc2
    in (Case e1' e2' (x, y, e3'), acc3)

lintCompAux (If e1 e2 e3) acc =
    let (e1', acc1) = lintCompAux e1 acc
        (e2', acc2) = lintCompAux e2 acc1
        (e3', acc3) = lintCompAux e3 acc2
    in (If e1' e2' e3', acc3)

lintCompAux expr acc = (expr, acc)

lintComp :: Linting Expr
lintComp expr = lintCompAux expr []


--------------------------------------------------------------------------------
-- Eta Redución
--------------------------------------------------------------------------------
-- se aplica en casos de la forma \x -> e x, reemplazando por e
-- Construye sugerencias de la forma (LintEta e r)
lintEtaAux :: Expr -> [LintSugg] -> (Expr, [LintSugg])
lintEtaAux (Lam x e) acc =
    let (e', acc1) = lintEtaAux e acc
    in 
        case e' of
            App e1 (Var x) -> 
                if x `elem` freeVariables e1 then 
                    (Lam x e', acc1)
                else (e1, acc1 ++ [LintEta (Lam x e) e1])
            _ -> (Lam x e', acc1)

lintEtaAux (Infix op e1 e2) acc =
    let (e1', acc1) = lintEtaAux e1 acc
        (e2', acc2) = lintEtaAux e2 acc1
    in (Infix op e1' e2', acc2)

lintEtaAux (App e1 e2) acc =
    let (e1', acc1) = lintEtaAux e1 acc
        (e2', acc2) = lintEtaAux e2 acc1
    in (App e1' e2', acc2)

lintEtaAux (Case e1 e2 (x, y, e3)) acc =
    let (e1', acc1) = lintEtaAux e1 acc
        (e2', acc2) = lintEtaAux e2 acc1
        (e3', acc3) = lintEtaAux e3 acc2
    in (Case e1' e2' (x, y, e3'), acc3)

lintEtaAux (If e1 e2 e3) acc =
    let (e1', acc1) = lintEtaAux e1 acc
        (e2', acc2) = lintEtaAux e2 acc1
        (e3', acc3) = lintEtaAux e3 acc2
    in (If e1' e2' e3', acc3)

lintEtaAux expr acc = (expr, acc)

lintEta :: Linting Expr
lintEta expr = lintEtaAux expr [] 


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
