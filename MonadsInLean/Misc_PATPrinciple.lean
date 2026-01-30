/- In this file, I have some examples I use to illustrate the Curry-Howard Correspondence,
which I first leant as the PAT Principle, which reads as either one of:
1) Propositions as Types
2) Proofs as Terms
-/


/- **Section 1** Try finding elements, or inhabitants of the following types by filling in the
sorries with terms of the correct type.-/

def inhabitant_1 (α β : Type) : (α → β) → α → β := sorry

def inhabitant_2 (α β γ : Type) : (α → β) → (β → γ) → (α → γ) := sorry

def inhabitant_3 (α β γ : Type) : (α → β → γ) → ((β → α) → β) → α → γ := sorry



/- **Section 2** Try finding proofs for the following propositions. You may enter tactic mode,
but try writing out a proof term directly first.-/

theorem first (A B : Prop) : (A → B) → A → B := sorry

theorem second (A B C : Prop) : (A → B) → (B → C) → (A → C) := sorry

theorem third (A B C : Prop) : (A → B → C) → ((B → A) → B) → A → C := sorry

/- Did you notice anything similar about both sections? This is the Curry-Howard correspondence
in action. -/
