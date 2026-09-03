import Verbose.French.ExampleLib
import MAT120.lois_logique

open Verbose.French

example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  with_suggestions
    exact hPQ hP

/- First, introduce basic LEAN commands
- Natural numbers, real numbes, integers, ...
- Quantifiers ∃ ∀ (syntax)
- Exercises syntax
- Explain the LEAN infoview
- sorry - proof by apology

Notes from Thomas: Language of math will be seen in class in the second week: "This is not a phrase in set theory and logic, you have to translate"
-/

/- Things like this to see in the second week-/
Exemple "Exemple 1.6 des notes de cours"
 Données : (n : ℕ)
 Hypothèses : (h : (∃ k : ℕ, n = k*4)) /- n est divisible par 4 -/
 Conclusion : (∃ k' : ℕ, n = k'*2) /- n est pair -/
Démonstration :
 Par h on obtient k tel que (hk : n = k*4) /-Attention : LEAN ne sait pas que l*4 = 4*l-/
 Montrons que k*2 convient /- k*2 = k'-/
 Calc n = k*4 par hk
      _ = k*2*2 par calcul /- Please write in your code what you use? -/
QED

/- Ecrire sa contraposée-/

Exemple "Contraposée"
Données : (n : ℕ)
Hypothèses :
Conclusion : (∀ k : ℕ, n ≠ k*2) → (∀ k' : ℕ, n ≠ k'*4)
Démonstration :
  On contrapose
  sorry
QED


/- This type of examples will be seen in the first 2hour class Tuesday 8h30-10h20-/

example (P Q : Prop) (hP : P) (h : P → Q) : Q := sorry

Exemple "Propositional logic in an example bloc"
 Données : (P Q : Prop)
 Hypothèses : (hp : P) (imp : P → Q)
 Conclusion : Q
Démonstration :
 Par imp il suffit de montrer que P
 On conclut par hp
QED


/- En utilisant seulement les lois de LP-1 à LP-13-/
Exemple "Laboratoire 4 1)"
  Données : (A B : Prop)
  Hypothèses :
  Conclusion : (A ∨ (A ∧ B)) ↔ A
Démonstration :
On réécrit via LP_12
On réécrit via LP_6
On réécrit via LP_11
On réécrit via LP_5
On réécrit via LP_14
QED
