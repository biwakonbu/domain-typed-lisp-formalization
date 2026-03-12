namespace DomainTypedLispFormalization

abbrev Name := String

inductive DTLType where
  | bool
  | int
  | symbol
  | domain (name : Name)
  | adt (name : Name)
  | func (args : List DTLType) (ret : DTLType)
  | refine (var : Name) (base : DTLType) (predicateName : Name)
  deriving Repr

inductive Pattern where
  | wildcard
  | var (name : Name)
  | boolLit (value : Bool)
  | intLit (value : Int)
  | ctor (name : Name) (fields : List Pattern)
  deriving Repr

inductive Expr where
  | var (name : Name)
  | symbol (value : Name)
  | int (value : Int)
  | bool (value : Bool)
  | call (name : Name) (args : List Expr)
  | letE (bindings : List (Name × Expr)) (body : Expr)
  | ifE (cond : Expr) (thenBranch : Expr) (elseBranch : Expr)
  | matchE (scrutinee : Expr) (arms : List (Pattern × Expr))
  deriving Repr

inductive Term where
  | var (name : Name)
  | symbol (value : Name)
  | int (value : Int)
  | bool (value : Bool)
  | ctor (name : Name) (args : List Term)
  deriving Repr

inductive Formula where
  | triv
  | pred (name : Name) (args : List Term)
  | andF (goals : List Formula)
  | notF (goal : Formula)
  deriving Repr

structure Atom where
  pred : Name
  terms : List Term
  deriving Repr

structure Rule where
  head : Atom
  body : Formula
  deriving Repr

end DomainTypedLispFormalization
