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

structure Theorem where
  hypotheses : List Term
  conclusion : Term

def and_intro (l : Theorem) (r : Theorem) : Theorem :=
  ⟨l.hypotheses ++ r.hypotheses, .And l.conclusion r.conclusion⟩

def and_elim_l (t : Theorem) : Option Theorem :=
  match t.conclusion with
  | .And l _ => pure ⟨t.hypotheses, l⟩
  | _ => none

def and_elim_r (t : Theorem) : Option Theorem :=
  match t.conclusion with
  | .And _ r => pure ⟨t.hypotheses, r⟩
  | _ => none


end LCF
