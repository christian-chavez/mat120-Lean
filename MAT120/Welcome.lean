import Verbose.French.ExampleLib

open Verbose.French

example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  with_suggestions
    exact hPQ hP

Exemple "Exemple 1.16 des notes de cours"
 Données : (n : ℕ)
 Hypothèses : (hdivisible : (∃ k : ℕ, n = k*4))
 Conclusion : (∃ k' : ℕ, n = k*2)
Démonstration :
 Par hdivisible on obtient (l : ℕ) tel que (hl : n = 4*l)
 Montrons que l*2 convient
 On calcule
QED
/- Par hdivisible on obtient k tel que -/
