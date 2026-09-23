import Verbose.French.ExampleLib
import MAT120.src.lois_logique
import MAT120.src.calcul
import Mathlib.Analysis.Real.Sqrt

open Verbose.French
open Verbose.Named


Lemme comb_lin "Combinaison linéaire de diviseurs (ex 2.35)"
  Données : {a b d : ℤ }
  Hypothèses : (Hda : d ∣ a) (Hdb : d ∣ b)
  Conclusion : ∀ u v : ℤ, d ∣ (a*u + b*v)
Démonstration :
  Soit u v : ℤ
  Par Hda on obtient (k : ℤ) tel que (H1 : a = d*k)
  Par Hdb on obtient (l : ℤ) tel que (H2 : b = d*l)
  Montrons que k*u + l*v convient
  Calc a*u + b*v = (d*k)*u + b*v      par H1
      _          = (d*k)*u + (d*l)*v  par H2
      _          = d*(k*u+l*v)        par calcul
QED


Exemple "Réutilisation de comb_lin"
  Données : (a b d : ℤ )
  Hypothèses : (h1 : d∣ a) (h2: d ∣ b)
  Conclusion : d ∣ (a-b)
Démonstration :
  Fait hyp : a - b = a*1 + b*(-1) par calcul
  On réécrit via hyp
  On conclut par comb_lin appliqué à h1 et h2 et 1 et (-1)
QED


Exemple "n pair si et selement si n+4 pair"
  Données : (n : ℤ )
  Hypothèses :
  Conclusion : (∃ k : ℤ, n = 2*k) ↔ (∃ k' : ℤ, n+4 = 2*k')
Démonstration :
  Montrons d'abord que (∃ k : ℤ, n = 2*k) →  (∃ k' : ℤ, n+4 = 2*k')
  Supposons h : ∃ k : ℤ, n=2*k
  Par h on obtient (k : ℤ ) tel que (hk: n=2*k)
  Montrons que k+2 convient
  Calc n+4 = 2*k +4 par hk
    _      = 2*(k+2) par calcul
  Montrons maintenant que (∃ k' : ℤ, n+4 = 2*k') → (∃ k : ℤ, n = 2*k)
  Supposons h : ∃ k' : ℤ, n+4 = 2*k'
  Par h on obtient (k' : ℤ ) tel que (hk' : n+4 = 2*k')
  Montrons que k'-2 convient
  Calc n=2*k'-4 par hk'
    _   =2*(k'-2) par calcul
QED
