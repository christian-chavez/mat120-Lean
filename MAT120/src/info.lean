
-- ######### TACTIQUES

/- VerboseLEAN vient avec un tactique "on calcule" "par calcul" de base qui admet plusiers resultas de base sur les nombres réels et entieres. On a crée une nouvelle tactique "on calcule avec" qui permet de faire des calculs avec des hypotheses.

Pour l'utiliser, il faut écrire

import MAT120.src.calcul

au début du fichier

Exemple:

Exemple "Preuve par contradiction"
  Données : (x : ℝ) (y : ℝ)
  Hypothèses : (hxy : x ≠ y) (hx : x > 0) (hy : y > 0)
  Conclusion : x/y + y/x > 2
Démonstration :
  Supposons par l'absurde h : x/y + y/x ≤ 2
  Fait hxy' : x - y ≠ 0 car on calcule avec hxy -- `Fait` + `par`
  Fait lz : (x-y)^2 > 0  car on calcule avec hxy' -- par sq_pos_of_ne_zero appliqué à hxy'
  Fait k : x*y > 0 car
    Calc x*y > 0*y par hx
        _ = 0 par calcul
  Fait h' : x/y + y/x - 2 ≤ 0 car on calcule avec h
  Fait e : (x-y)^2 ≤ 0 car
    Calc (x-y)^2 = x^2+y^2 -2*x*y par calcul
      _ = (x/y+y/x-2)*(x*y) car on calcule avec k
      _ ≤ 0*(x*y) par h'
      _ ≤ 0 par k
  On combine e et lz
QED
-/

-- ######### LEMMES

/-

Example de lemme en LEAN qui être utilisée par la suite

Lemme somme_lemme "description"
  Données :
  Hypothèses :
  Conclusion :
Démonstration :
  ...
QED

-/
