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

#check @Term.rec

structure Theorem where
  -- NOTE: the head of this list is the last element of the hypotheses
  hypotheses : List Term
  conclusion : Term
deriving Repr

-- map LCF terms into lean props.
def mapTerm (assign : String → Prop) : (t : Term) → Prop
| .Var s => assign s
| .True => True
| .False => False
| .And l r => (mapTerm assign l) ∧ (mapTerm assign r)
| .Or l r => (mapTerm assign l) ∨ (mapTerm assign r)
| .Neg t => ¬ (mapTerm assign t)
| .Impl l r => (mapTerm assign l) → (mapTerm assign r)

-- construct the lean prop that asserts the validity of the input theorem
def valid (t : Theorem) : Prop :=
  ∀ (a : String → Prop), (∀ (p : Prop), p ∈ List.map (mapTerm a) t.hypotheses → p) → mapTerm a t.conclusion

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

theorem and_intro_sound (l r : Theorem) (hl : valid l) (hr : valid r) : valid (and_intro l r) := by
  unfold and_intro

  unfold valid at *
  intro assign
  intro hyp_valid
  simp at *
  unfold mapTerm

  have hyp_l : ∀ (p : Prop), (∃ a ∈ l.hypotheses, mapTerm assign a ↔ p) → p := by
    clear hl hr
    intro p
    specialize hyp_valid p
    aesop
  have hyp_r : ∀ (p : Prop), (∃ a ∈ r.hypotheses, mapTerm assign a ↔ p) → p := by
    clear hl hr hyp_l
    intro p
    specialize hyp_valid p
    aesop

  have hl' : (∀ (p : Prop), ∀ x ∈ l.hypotheses, (mapTerm assign x ↔ p) → p) := by
    clear hl hr hyp_valid hyp_r
    aesop
  have hr' : (∀ (p : Prop), ∀ x ∈ r.hypotheses, (mapTerm assign x ↔ p) → p) := by
    clear hl hr hyp_valid hyp_l
    aesop

  clear hyp_valid
  specialize hl assign hl'
  specialize hr assign hr'
  clear hyp_l hyp_r hl' hr'
  simp [*]

def or_intro_l (l : Theorem) (t : Term) : Theorem :=
  ⟨l.hypotheses, Term.Or l.conclusion t⟩

theorem or_intro_l_valid (l : Theorem) (t : Term) (hl : valid l) : valid (or_intro_l l t) := by
  unfold valid at *
  unfold or_intro_l
  intros assign hyp_valid
  simp at *
  specialize hl assign
  unfold mapTerm
  apply Or.intro_left
  specialize hl hyp_valid
  assumption

def or_intro_r (r : Theorem) (t : Term) : Theorem :=
  ⟨r.hypotheses, Term.Or t r.conclusion⟩

theorem or_intro_r_valid (r : Theorem) (t : Term) (hr : valid r) : valid (or_intro_r r t) := by
  unfold valid at *
  unfold or_intro_r
  intros assign hyp_valid
  simp at *
  specialize hr assign
  unfold mapTerm
  apply Or.intro_right
  specialize hr hyp_valid
  assumption

def true : Theorem := ⟨[], Term.True⟩

theorem true_valid : valid true := by simp [valid, true, mapTerm]

def assume (t : Term) : Theorem := ⟨[t], t⟩

theorem assume_valid (t : Term) : valid (LCF.assume t) := by
  simp [valid, LCF.assume, mapTerm]
  aesop

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

theorem subst_preserves_validity (var : String) (t : Term) (hyps : List Term) (conclusion : Term) (ht : valid ⟨hyps, conclusion⟩) : valid ⟨List.map (subst var t) hyps, subst var t conclusion⟩ := by
  unfold valid at *
  intro assign
  let assign' := λ var' => if var = var' then mapTerm assign t else assign var'
  specialize ht assign'
  have mapTermPres : ∀ (t' : Term), mapTerm assign' t' = mapTerm assign (subst var t t') := by
    intro t'
    induction t' with
    | Var s =>
      dsimp [assign']
      rw (config := {occs := .pos [1]}) [mapTerm]
      simp_all
      split
      case Var.isTrue h =>
        unfold subst
        simp_all
      case Var.isFalse h =>
        unfold subst
        have nes : ¬ (s = var) := by aesop
        simp_all
        unfold mapTerm
        rfl
    | True => aesop
    | False => aesop
    | And l r hl hr => unfold mapTerm subst; simp_all
    | Or l r hl hr => unfold mapTerm subst; simp_all
    | Neg t ih => unfold mapTerm subst; simp_all
    | Impl l r hl hr => unfold mapTerm subst; simp_all

  induction hyps with
  | nil => aesop
  | cons hd tl ih_hyp =>
    simp [*] at *
    exact ht

theorem instantiate_valid (var : String) (t : Term) (thm : Theorem) (ht : valid thm)
  : match instantiate var t thm with
    | .none => True
    | .some res => valid res
  := by
    unfold instantiate
    split
    case h_1 => trivial
    case h_2 x res heq =>
      simp_all
      unfold valid
      have x_not_free : ¬ (∃ x ∈ thm.hypotheses, occurs_free var x = Bool.true) := by aesop
      have res_eq : res = { hypotheses := thm.hypotheses, conclusion := subst var t thm.conclusion } := by aesop
      clear heq
      intros assign hyp_valid
      rw [res_eq] at hyp_valid ⊢
      simp [*] at hyp_valid ⊢
      have subst_valid : valid ⟨List.map (subst var t) thm.hypotheses, subst var t thm.conclusion⟩ := subst_preserves_validity var t thm.hypotheses thm.conclusion ht
      unfold valid at subst_valid
      simp at subst_valid
      specialize subst_valid assign
      refine subst_valid ?h
      intro p x hx
      have not_free : ¬ (occurs_free var x) := by aesop
      have subst_noop : subst var t x = x := by
        clear hx
        induction x with
        | Var s' =>
          unfold occurs_free at not_free
          simp [subst]
          aesop
        | True => trivial
        | False => trivial
        | And l r hl hr =>
          unfold subst
          simp
          apply And.intro
          · unfold occurs_free at not_free
            aesop
          · unfold occurs_free at not_free
            aesop
        | Or l r hl hr =>
          unfold subst
          simp
          apply And.intro
          · unfold occurs_free at not_free
            aesop
          · unfold occurs_free at not_free
            aesop
        | Neg t' ht' =>
          unfold subst
          simp
          unfold occurs_free at not_free
          aesop
        | Impl l r hl hr =>
          unfold subst
          simp
          apply And.intro
          · unfold occurs_free at not_free
            aesop
          · unfold occurs_free at not_free
            aesop
      aesop

-- Structural --

-- This applies all structural rules at once
def structural (thm : Theorem) (reordered : List Term) : Option Theorem :=
  if List.toFinset thm.hypotheses ⊆ List.toFinset reordered
  then pure ⟨reordered, thm.conclusion⟩
  else none

theorem structural_valid (t : Theorem) (reord : List Term) (ht : valid t) :
  match structural t reord with
    | .none => True
    | .some res => valid res
  := by
    unfold structural
    split
    case h_1 => trivial
    case h_2 x res heq =>
      simp_all
      unfold valid
      intros assign hyp_valid
      rcases heq with ⟨hl, hr⟩
      symm at hr
      rw [hr]
      rw [hr] at hyp_valid
      simp_all
      have valid_hyps : ∀ (p : Prop), ∀ x ∈ t.hypotheses, (mapTerm assign x ↔ p) → p := by
        intros p x hx
        specialize hyp_valid p
        have : x ∈ reord := by
          clear hr hyp_valid
          have : x ∈ t.hypotheses → x ∈ t.hypotheses.toFinset := by aesop
          have : x ∈ t.hypotheses.toFinset → x ∈ reord.toFinset := by
            unfold Finset.instHasSubset at hl
            aesop
          aesop
        aesop
      unfold valid at ht
      specialize ht assign
      have valid_hyps' : (∀ p ∈ List.map (mapTerm assign) t.hypotheses, p) := by
        clear hyp_valid hl hr ht
        aesop
      exact ht valid_hyps'

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
