import Verbose.French.ExampleLib

open Verbose.French
open Verbose.Named

/- ======================================================================
   PROJET LEAN B — Divisibilité
   ======================================================================

   Définition :
     a ∣ b  veut dire  ∃ k : ℤ, b = a*k

   PARTIE LEAN : remplacer chaque `sorry` par une preuve.
     a) Si a ∣ b, alors a ∣ bc.
     b) Si 3 ∣ n, alors 9 ∣ n².
     c) Si n² n'est pas divisible par 9, alors n n'est pas divisible par 3
        (preuve par contraposée).
     d) Réfuter : « si a ∣ b, alors a ≤ b ».

   ======================================================================

   AIDE-MÉMOIRE

   Symboles (taper le code, puis espace) :
     ℤ \Z     ∣ \dvd (pas la barre | du clavier)     ∃ \exists
     ∀ \forall     ¬ \not     → \to     ≠ \ne     ≤ \le
     n² s'écrit n^2      bc s'écrit b*c

   Commandes :
     Par h on obtient (k : ℤ) tel que (hk : b = a*k)
         utilise une hypothèse h : a ∣ b (nomme k et son équation)
     Montrons que x convient
         prouve un but a ∣ b (ou ∃ k, ...) en prenant k = x
     Calc a = b par hk
          _ = c par calcul
         chaîne d'égalités : `par hk` utilise hk, `par calcul` fait l'algèbre
     On contrapose
         transforme le but P → Q en ¬Q → ¬P (et simplifie les négations)
     Supposons h : P
         pour prouver P → Q : on suppose P, il reste Q
     On pousse la négation
         transforme ¬ (∀ x, ...) en ∃ x, ¬ (...)
     Montrons d'abord que P  /  Montrons maintenant que Q
         prouve un but P ∧ Q en deux étapes
     On calcule
         vérifie un calcul avec des nombres

   La preuve est finie quand l'infoview affiche « No goals ».
-/


/- a) -/
Exemple "Si a divise b, alors a divise bc"
  Données : (a b c : ℤ)
  Hypothèses : (h : a ∣ b)
  Conclusion : a ∣ b*c
Démonstration :
  sorry
QED

/- b) -/
Exemple "Si 3 divise n, alors 9 divise n²"
  Données : (n : ℤ)
  Hypothèses : (h : (3 : ℤ) ∣ n)
  Conclusion : (9 : ℤ) ∣ n^2
Démonstration :
  sorry
QED

/- c) Indice : commencer par `On contrapose`. -/
Exemple "Si 9 ne divise pas n², alors 3 ne divise pas n"
  Données : (n : ℤ)
  Hypothèses :
  Conclusion : (∀ k : ℤ, n^2 ≠ 9*k) → (∀ k' : ℤ, n ≠ 3*k')
Démonstration :
  sorry
QED

/- d) Indice : penser aux nombres négatifs. -/
Exemple "Réfuter : si a divise b, alors a ≤ b"
  Données :
  Hypothèses :
  Conclusion : ¬ (∀ a b : ℤ, a ∣ b → a ≤ b)
Démonstration :
  sorry
QED
