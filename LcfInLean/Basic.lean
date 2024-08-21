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
  -- NOTE: the head of this list is the last element of the hypotheses
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
  | ⟨d_hs, .Or l r⟩, ⟨l_lst :: l_hs, lgl⟩, ⟨r_lst :: r_hs, rgl⟩ =>
    if lgl != rgl || l_lst != l || r_lst != r
    then none
    else pure ⟨d_hs ++ l_hs ++ r_hs, lgl⟩
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

-- This applies all structural rules at once
def structural (thm : Theorem) (reordered : List Term) : Option Theorem :=
  if List.toFinset thm.hypotheses ⊆ List.toFinset reordered
  then pure ⟨reordered, thm.conclusion⟩
  else none

-- the following are meta proofs that the above covers all structural rules,
-- carried out by implementing the individual rules in terms of the above

theorem contraction (t : Term) (ts : List Term) (gl : Term)
  : structural ⟨t :: t :: ts, gl⟩ (t :: ts) = some ⟨t :: ts, gl⟩ := by
    unfold structural
    simp

theorem weakening (t : Term) (hyps : List Term) (gl : Term)
  : structural ⟨hyps, gl⟩ (t :: hyps) = some ⟨t :: hyps, gl⟩ := by
    unfold structural
    simp

theorem exchange (Γ₁ : List Term) (A : Term) (Γ₂ : List Term) (B : Term) (Γ₃ : List Term) (gl : Term)
  : structural ⟨Γ₁ ++ [A] ++ Γ₂ ++ [B] ++ Γ₃, gl⟩ (Γ₁ ++ [B] ++ Γ₂ ++ [A] ++ Γ₃)
  = some ⟨Γ₁ ++ [B] ++ Γ₂ ++ [A] ++ Γ₃, gl⟩ := by
    unfold structural
    have : insert A (insert B (Γ₁.toFinset ∪ (Γ₂.toFinset ∪ Γ₃.toFinset))) = insert B (insert A (Γ₁.toFinset ∪ (Γ₂.toFinset ∪ Γ₃.toFinset))) := by aesop
    aesop

/-
 - TODO: prove that structural only does contraction, weakening, and exchange:
 -   - to state the theorem we would wanna state the above as relations and then the theorem would state that if the structural relation holds then there is a chain of the other relations that holds transitively
     - to prove we would define a routine that applies all structural rules until no more can be applied (notice that exchange makes this rewrite system confluent):
     - prove that if the subset condition in structural holds then our routine always finds a chain
 -/

-- Proofs --

-- p -> p ∎
#eval (discharge (.Var "p") $ assume (.Var "p"))

-- TODO: prove some de morgans stuff

end LCF
