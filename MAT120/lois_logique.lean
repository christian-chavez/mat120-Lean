import Verbose.French.ExampleLib

open Verbose.French

/- Table 1. Lois de ∨, ∧ et ¬ -/

-- élément absorbant et
lemma LP_1
(A : Prop) : (A ∧ false) ↔ false := by simp

-- élément absorbant ou
lemma LP_2
(A : Prop) : (A ∨ true) ↔ true := by simp

-- élement neutre et
lemma LP_3
(A : Prop) : (A ∧ true) ↔ A := by simp

-- élement neutre ou
lemma LP_4
(A : Prop) : (A ∨ false) ↔ A := by simp

-- idempotence et
lemma LP_5
(A : Prop) : (A ∧ A) ↔ A := by simp

-- idempotence ou
lemma LP_6
(A : Prop) : (A ∨ A) ↔ A := by simp

-- commutativité et
lemma LP_7
(A B: Prop) : (A ∧ B) ↔ (B ∧ A) := by grind

-- commutativité ou
lemma LP_8
(A B: Prop) : (A ∨ B) ↔ (B ∨ A) := by grind

-- associativité et
lemma LP_9
(A B C : Prop) : (A ∧ (B ∧ C)) ↔ ((A ∧ B) ∧ C) := by grind

-- associativité ou
lemma LP_10
(A B C : Prop) : (A ∨ (B ∨ C)) ↔ ((A ∨ B) ∨ C) := by grind

-- distributivité et sur ou
lemma LP_11
(A B C : Prop) : (A ∧ (B ∨ C)) ↔ ((A ∧ B) ∨ (A ∧ C)) := by grind

-- distributivité ou sur et
lemma LP_12
(A B C : Prop) : (A ∨ (B ∧ C)) ↔ ((A ∨ B) ∧ (A ∨ C)) := by grind

-- absorbtion et sur ou
lemma LP_13
(A B : Prop) : (A ∧ (A ∨ B)) ↔ A := by grind

-- absorbtion ou sur et
lemma LP_14
(A B : Prop) : (A ∨ (A ∧ B)) ↔ A := by grind

-- absorbtion et avec négation
lemma LP_15
(A B : Prop) : (A ∧ (¬A ∨ B)) ↔ (A ∧ B) := by grind

-- absorbtion ou avec négation
lemma LP_16
(A B : Prop) : (A ∨ (¬A ∧ B)) ↔ (A ∨ B) := by grind

-- De Morgan négation et
lemma LP_17
(A B : Prop) : ¬(A ∧ B) ↔ (¬A ∨ ¬B) := by grind

-- De Morgan négation ou
lemma LP_18
(A B : Prop) : ¬(A ∨ B) ↔ (¬A ∧ ¬B) := by grind

-- contradiction
lemma LP_19
(A : Prop) : (A ∧ ¬A) ↔ false := by simp

-- tiers exclu
lemma LP_20
(A : Prop) : (A ∨ ¬A) ↔ true := by tauto

-- involution
lemma LP_21
(A : Prop) : ¬¬A ↔ A := by simp

/- Table 2. Lois de → -/

-- implication-comme-disjonction
lemma LP_22
(A B : Prop) : (A → B) ↔ (¬A ∨ B) := by grind

-- implication-comme-tiers-exclu
lemma LP_23
(A : Prop) : (A → A) ↔ true := by simp

-- implication-comme-négation et
lemma LP_24
(A B : Prop) : (A → B) ↔ ¬(A ∧ ¬B) := by grind

-- négation implication
lemma LP_25
(A B : Prop) : ¬(A → B) ↔ (A ∧ ¬B) := by grind

-- Contraposée
lemma LP_26
(A B : Prop) : (A → B) ↔ (¬B → ¬A) := by grind

-- implication divers 1
lemma LP_27
(A : Prop) : (A → true) ↔ true := by simp

-- implication divers 2
lemma LP_28
(A : Prop) : (true → A) ↔ A := by simp

-- implication divers 3
lemma LP_29
(A : Prop) : (A → false) ↔ ¬A := by simp

-- implication divers 4
lemma LP_30
(A : Prop) : (false → A) ↔ true := by simp

-- implication divers 5
lemma LP_31
(A : Prop) : (A → ¬A) ↔ ¬A := by grind

-- implication divers 6
lemma LP_32
(A : Prop) : (¬A → A) ↔ A := by grind

-- distributivité implication et gauche
lemma LP_33
(A B C : Prop) : (C → (A ∧ B)) ↔ ((C → A) ∧ (C → B)) := by grind

-- distributivité implication ou gauche
lemma LP_34
(A B C : Prop) : (C → (A ∨ B)) ↔ ((C → A) ∨ (C → B)) := by grind

-- distributivité implication et droite
lemma LP_35
(A B C : Prop) : ((A ∧ B) → C) ↔ ((A → C) ∨ (B → C)) := by grind

-- distributivité implication ou droite
lemma LP_36
(A B C : Prop) : ((A ∨ B) → C) ↔ ((A → C) ∧ (B → C)) := by grind

-- implication conjonction 1
lemma LP_37
(A B C : Prop) : (A → (B → C)) ↔ ((A ∧ B) → C) := by grind

-- implication conjonction 2
lemma LP_38
(A B C : Prop) : (A → (B → C)) ↔ (B → (A → C)) := by grind

-- définition par cas
lemma LP_39
(A B C : Prop) : ((A → B) ∧ (¬A → C)) ↔ ((A ∧ B) ∨ (¬A ∧ C)) := by grind

/- Table 3. Lois de ↔ -/

-- équivalence-comme-implication
lemma LP_40
(A B : Prop) : (A ↔ B) ↔ ((A → B) ∧ (B → A)) := by grind

-- équivalence-comme-ou
lemma LP_41
(A B : Prop) : (A ↔ B) ↔ ((A ∧ B) ∨ ¬(A ∨ B)) := by grind

-- équivalence-comme-négation
lemma LP_42
(A B : Prop) : (A ↔ B) ↔ (¬A ↔ ¬B) := by grind

-- commutativité de l'équivalence
lemma LP_43
(A B : Prop) : (A ↔ B) ↔ (B ↔ A) := by grind

-- associativité de l'équivalence
lemma LP_44
(A B C : Prop) : (A ↔ (B ↔ C)) ↔ ((A ↔ B) ↔ C) := by grind

-- équivalence divers 1
lemma LP_45
(A : Prop) : (A ↔ A) ↔ true := by simp

-- équivalence divers 2
lemma LP_46
(A : Prop) : (A ↔ ¬A) ↔ false := by grind

-- équivalence divers 3
lemma LP_47
(A : Prop) : (A ↔ true) ↔ A := by simp

-- équivalence divers 4
lemma LP_48
(A : Prop) : (A ↔ false) ↔ ¬A := by simp

-- équivalence divers 5
lemma LP_49
(A B : Prop) : (A → B) ↔ (A ↔ (A ∧ B)) := by grind

-- équivalence divers 6
lemma LP_50
(A B : Prop) : (A → B) ↔ (B ↔ (A ∨ B)) := by grind

-- équivalence divers 7
lemma LP_51
(A B C : Prop) : (A ∨ (B ↔ C)) ↔ ((A ∨ B) ↔ (A ∨ C)) := by grind
