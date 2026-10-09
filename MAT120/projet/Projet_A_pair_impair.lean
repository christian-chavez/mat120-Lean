import Verbose.French.ExampleLib

open Verbose.French
open Verbose.Named

/- ======================================================================
   PROJET LEAN A — Pair et impair
   ===================================================================

   Définitions (à utiliser telles quelles) :
     n est pair   :  ∃ k : ℤ, n = 2*k
     n est impair :  ∃ k : ℤ, n = 2*k+1

   PARTIE LEAN (remplacer chaque `sorry`)
     a) La somme de deux entiers pairs est paire.
     b) La somme d'un entier pair et d'un entier impair est impaire.
     c) Le carré d'un entier impair est impair.
     e) Réfuter : « pour tout entier n, n² ≥ 2n ».

   PARTIE ÉCRITE: Rédiger d'abord la preuve de chaque un en papier., comme dans les notes.
   =================================================================

Rappel des commandes utiles
     Par h on obtient (k : ℤ) tel que (hk : n = 2*k)
     Montrons que ... convient
     Calc ... = ... par hk
          _   = ... par calcul
     On discute en utilisant h        (quand h : P ∨ Q)
     Supposons hp : P
     On pousse la négation
     On calcule
-/


/- a) -/
Exemple "Pair + pair = pair"
  Données : (n m : ℤ)
  Hypothèses : (hn : ∃ k : ℤ, n = 2*k) (hm : ∃ k : ℤ, m = 2*k)
  Conclusion : ∃ k : ℤ, n + m = 2*k
Démonstration :
  sorry
QED

/- b) -/
Exemple "Pair + impair = impair"
  Données : (n m : ℤ)
  Hypothèses : (hn : ∃ k : ℤ, n = 2*k) (hm : ∃ k : ℤ, m = 2*k+1)
  Conclusion : ∃ k : ℤ, n + m = 2*k+1
Démonstration :
  sorry
QED

/- c) -/
Exemple "Le carré d'un impair est impair"
  Données : (n : ℤ)
  Hypothèses : (hn : ∃ k : ℤ, n = 2*k+1)
  Conclusion : ∃ k' : ℤ, n^2 = 2*k'+1
Démonstration :
  sorry
QED

/- d) On admet que tout entier est pair ou impair (hypothèse `parité`).
   Indice : traiter les deux cas séparément. -/
Exemple "n² + n est toujours pair"
  Données : (n : ℤ)
  Hypothèses : (parité : (∃ k : ℤ, n = 2*k) ∨ (∃ k : ℤ, n = 2*k+1))
  Conclusion : ∃ k' : ℤ, n^2 + n = 2*k'
Démonstration :
  sorry
QED

/- e) -/
Exemple "Réfuter : pour tout n, n² ≥ 2n"
  Données :
  Hypothèses :
  Conclusion : ¬ (∀ n : ℤ, n^2 ≥ 2*n)
Démonstration :
  sorry
QED
