import DomainTypedLispFormalization.CoreValues

namespace DomainTypedLispFormalization

def evalTerm (_env : Env) (_term : Term) : Option Value := none

def evalFormula (_facts : DerivedFacts) (_env : Env) (_formula : Formula) : Prop := True

def selectMatchArm (_value : Value) (_arms : List (Pattern × Expr)) : Option Expr := none

def evalExpr (_facts : DerivedFacts) (_env : Env) (_expr : Expr) : Option Value := none

axiom formula_eval_deterministic : Prop
axiom pattern_match_deterministic : Prop
axiom expr_eval_deterministic : Prop

end DomainTypedLispFormalization
