import Mathlib.Data.Finset.Basic

namespace LCF

-- Sentences in Propositional Logic
inductive Term where
| Var (s : String)
| True
| False
| And (l : Term) (r : Term)
| Or (l : Term) (r : Term)
| Neg (t : Term)
| Impl (l : Term) (r : Term)
deriving BEq, DecidableEq, Repr

structure Theorem where
  hypotheses : List Term
  conclusion : Term
deriving Repr

-- Utils --

def occurs_free (nm : String) : (t : Term) → Bool
| .Var s => s == nm
| .True => False
| .False => False
| .And l r => occurs_free nm l || occurs_free nm r
| .Or l r => occurs_free nm l || occurs_free nm r
| .Neg t => occurs_free nm t
| .Impl l r => occurs_free nm l || occurs_free nm r

-- Invariant: nm must not be free in t
def subst (nm : String) (t : Term) : (target : Term) → Term
| .Var s => if s == nm then t else .Var s
| .True => .True
| .False => .False
| .And l r => .And (subst nm t l) (subst nm t r)
| .Or l r => .Or (subst nm t l) (subst nm t r)
| .Neg t' => .Neg (subst nm t t')
| .Impl l r => .Impl (subst nm t l) (subst nm t r)

-- Introduction Rules --

def and_intro (l : Theorem) (r : Theorem) : Theorem :=
  ⟨l.hypotheses ++ r.hypotheses, .And l.conclusion r.conclusion⟩

def or_intro_l (l : Theorem) (t : Term) : Theorem :=
  ⟨l.hypotheses, Term.Or l.conclusion t⟩

def or_intro_r (r : Theorem) (t : Term) : Theorem :=
  ⟨r.hypotheses, Term.Or t r.conclusion⟩

def true : Theorem := ⟨[], Term.True⟩
def assume (t : Term) : Theorem := ⟨[t], t⟩

def discharge (a : Term) (thm : Theorem) : Theorem :=
  ⟨List.filter (λ h => h != a) thm.hypotheses
  , Term.Impl a thm.conclusion
  ⟩

-- Elimination Rules --

def and_elim_l (t : Theorem) : Option Theorem :=
  match t.conclusion with
  | .And l _ => pure ⟨t.hypotheses, l⟩
  | _ => none

def or_elim : (disjunct : Theorem) → (l_impl : Theorem) → (r_impl : Theorem) → Option Theorem
  | ⟨d_hs, .Or l r⟩, ⟨l_hs, lgl⟩, ⟨r_hs, rgl⟩ =>
    if lgl != rgl || List.getLast? l_hs != some l || List.getLast? r_hs != some r
    then none
    else pure ⟨d_hs ++ List.dropLast l_hs ++ List.dropLast r_hs, lgl⟩
  | _, _, _ => none

def and_elim_r (t : Theorem) : Option Theorem :=
  match t.conclusion with
  | .And _ r => pure ⟨t.hypotheses, r⟩
  | _ => none

def modus_ponens (imp : Theorem) (l : Theorem) : Option Theorem:=
  match imp.conclusion with
  | Term.Impl lhs rhs =>
    if l.conclusion != lhs
    then none
    else pure ⟨imp.hypotheses ++ l.hypotheses, rhs⟩
  | _ => none

-- Instantiation --

def instantiate (var : String) (t : Term) (thm : Theorem) : Option Theorem :=
  if List.any thm.hypotheses (occurs_free var)
  then none
  else pure ⟨thm.hypotheses, subst var t thm.conclusion⟩

-- Structural --

def structural (thm : Theorem) (reordered : List Term) : Option Theorem :=
  if List.toFinset thm.hypotheses ⊆ List.toFinset reordered
  then pure ⟨reordered, thm.conclusion⟩
  else none

-- Proofs --

-- p -> p ∎
#eval (discharge (.Var "p") $ assume (.Var "p"))

end LCF
