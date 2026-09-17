import Verbose.French.ExampleLib
import MAT120.src.lois_logique
import Mathlib.Analysis.Real.Sqrt

open Verbose.French
open Verbose.Named

/- Plan de la séance
- Rappels de mardi
- Comment écrire des commentaires
- Partir des définitions (pair, impair, divise, premier)
- Prouver une équivalence
- Réfuter un énoncé : le contre-exemple
- Preuve par contraposée
- Preuve par contradiction (l'absurde)
- Preuve par disjonction de cas
- Preuves d'existence et d'unicité
- Le principe des tiroirs
- Comment choisir une méthode ? Conseils de rédaction
- Exercices
-/

/- Rappel de mardi :
-/

#check (2=3 : Prop) -- Voici un commentaire de ligne
#check ((∃ x : ℕ, x = 1/2) : Prop)
#check (1/2 : ℕ)

/- Voici un commentaire en block
   Vous pouvez écrire plusieurs lignes dedans!
-/

Exemple "Démontrer que les deux ennoncés sont équivalents en utilisant seulement les régles LP_1 à LP_21"
  Données : (A B : Prop)
  Hypothèses :
  Conclusion : (A ∨ (A ∧ B)) ↔ A
Démonstration :
On réécrit via LP_12
-- Cette technique nous permet de réécrire une proposition avec une autre proposition équivalente.
sorry
QED

/- Les priorités des operations en LEAN et parenthéses -/

example (P Q : Prop)     : (¬ P ∧ Q)         ↔ ((¬ P) ∧ Q)            := Iff.rfl
example (P Q R : Prop)   : (P ∨ Q ∧ R)       ↔ (P ∨ (Q ∧ R))          := Iff.rfl
example (P Q R : Prop)   : (P ∧ Q → R)       ↔ ((P ∧ Q) → R)          := Iff.rfl
example (P Q R : Prop)   : (P → Q → R)       ↔ (P → (Q → R))          := Iff.rfl
example (P Q R : Prop)   : (P → Q ↔ R)       ↔ ((P → Q) ↔ R)          := Iff.rfl
example (P Q : ℕ → Prop) : (∀ x, P x ∧ Q x)  ↔ (∀ x, (P x ∧ Q x))     := Iff.rfl

/- Sans parenthèses, Lean les ajoute selon des priorités fixes,
   du plus « collant » au moins « collant » :
     ¬   puis   ∧   puis   ∨   puis   →   puis   ↔
   `→` s'associe à droite ; un quantificateur s'étend le plus loin possible. -/

/- Excercice : Formaliser l'ennoncé 1-c) du fichir lab_4.pdf dans un block VerboseLEAN-/


-- #####################################################################
/- Techniques de démonstration -/

/- 1. Preuve directe: partir des définitions

   Avant de prouver quoi que ce soit, il faut toujours revenir aux définitions :
     - n est pair s'il existe k ∈ ℤ tel que n = 2k.
     - n est impair s'il existe k ∈ ℤ tel que n = 2k + 1.
     - a divise b (noté a ∣ b) s'il existe k ∈ ℤ tel que b = ak.
   En LEAN, `a ∣ b` est déjà une notation pour `∃ k, b = a*k` (le symbole `∣` s'ecrit \dvd)
-/

Exemple "3 divise 12"
  Données :
  Hypothèses :
  Conclusion : (3 : ℕ) ∣ 12 -- Signification ∃ k : ℤ , 12 = 3*K
Démonstration :
  Montrons que 4 convient
  On calcule
QED

Exemple "Proposition 2.4"
  Données: (n : ℤ) -- Traduction:
  Hypothèses:
  Conclusion: (∃ k : ℤ, n = 2*k) → (∃ k' :ℤ, n^2 = 2*k') -- Traduction:
Démonstration:
 Supposons n_est_pair : (∃ k : ℤ, n = 2*k)
 Par n_est_pair on obtient k tel que (hn : n = 2*k) -- N'oubliez pas de donner un nom à vos hypothèses en LEAN
 Montrons que 2*k^2 convient -- k' = 2*k^2
 -- On doit faire des calculs, ce qu'on indique par `Calc`
 Calc n^2 = (2*k)^2 par hn
      _ = 4*(k^2) par calcul
      _ = 2*(2*k^2) par calcul
QED

/- À vos ordinateurs : Formaliser la preuve detaillée de l'excercice 2.29

Exemple "Prouver directement que le produit de deux entiers impairs est impair"
  Données:
  Hypothèses:
  Conclusion:
Démonstration:

QED
-/

/- 2. Prouver une équivalence

   Pour démontrer P ↔ Q, on prouve séparément P → Q et Q → P, avec
   `Montrons d'abord que ... / Montrons maintenant que ...` (déjà vu mardi).
-/

Exemple "n est pair si et seulement si n+2 est pair"
  Données : (n : ℤ)
  Hypothèses :
  Conclusion : (∃ k : ℤ, n = 2*k) ↔ (∃ k' : ℤ, n+2 = 2*k')
Démonstration :
  Montrons d'abord que (∃ k : ℤ, n = 2*k) → (∃ k' : ℤ, n+2 = 2*k')
  Supposons h : ∃ k : ℤ, n = 2*k
  Par h on obtient (k : ℤ) tel que (hk : n = 2*k)
  Montrons que k+1 convient
  Calc n+2 = 2*k+2   par hk
       _   = 2*(k+1) par calcul
  Montrons maintenant que (∃ k' : ℤ, n+2 = 2*k') → (∃ k : ℤ, n = 2*k)
  Supposons h : ∃ k' : ℤ, n+2 = 2*k'
  Par h on obtient (k' : ℤ) tel que (hk' : n+2 = 2*k')
  Montrons que k'-1 convient
  Calc n = 2*k'-2   par hk'
     _   = 2*(k'-1) par calcul
QED


/- À vos ordinateurs : Formaliser la preuve detaillée de l'excercice 2.30

Exemple "Prouver que pour tout n : ℤ, n est impair si et seulement si n^2 est impair"
  Données:
  Hypothèses:
  Conclusion:
Démonstration:

QED
-/

/- 3. Réfuter un énoncé : le contre-exemple

   Pour démontrer un énoncé universel ∀x P(x), un seul exemple ne suffit
   jamais. Mais pour le réfuter, un seul contre-exemple suffit. On combine
   `On pousse la négation` (¬∀ devient ∃¬) avec `Montrons que ... convient`.
-/

Exemple "Réfuter : a² = b² n'implique pas a = b"
  Données :
  Hypothèses :
  Conclusion : ¬ (∀ a b : ℝ, a^2 = b^2 → a = b) -- Traduction:
Démonstration :
  On pousse la négation -- ¬(P → Q) ↔ ?
  Montrons que (1:ℝ) convient
  Montrons que (-1:ℝ) convient -- On obtient un ennoncé de la forme P ∧ Q
  Montrons d'abord que (1:ℝ)^2 = (-1:ℝ)^2
  On calcule
  Montrons maintenant que (1:ℝ) ≠ (-1:ℝ)
  On calcule
QED


/- À vos ordinateurs : Formaliser et donner un contre-exemple de l'ennoncée de l'excercice 1.17 c)

Exemple "Excercice 1.17 c)"
  Données:
  Hypothèses:
  Conclusion:
Démonstration:

QED
-/

/- 4. Preuve d'une conjonction
  Dans l'excercice "Réfuter : a² = b² n'implique pas a = b", on a vu que pour démontrer un ennoncé de la forme P ∧ Q, on utilise la commande  `Montrons d'abord que P`... `Montrons maintenant que Q`...
-/

Exemple "4 divise 8 et 4 divise 12"
  Données :
  Hypothèses :
  Conclusion : (4:ℕ) ∣ 8 ∧ (4:ℕ) ∣ 12
Démonstration :
  Montrons d'abord que (4:ℕ) ∣ 8
  Montrons que 2 convient
  On calcule
  Montrons maintenant que (4:ℕ ) ∣ 12
  Montrons que 3 convient
  On calcule
QED

/- Utilisation d'une conjunction: si une de vos hypothéses est une conjoction, la commande pour l'utiliser est `Par (h : P ∧ Q), on obtient (hP : P) (hQ : Q) `-/

/- À vos ordinateurs : completer la preuve suivante: -/

Exemple "Transitivité de la division"
  Données : (a b c : ℕ)
  Hypothèses : (habc : (a : ℕ) ∣ b ∧ (b : ℕ )∣ c) -- P ∧ Q
  Conclusion : (a ∣ c)
Démonstration :
  Par habc on obtient ha hb  -- Traduction:
  sorry
QED


/- 5. Preuve par contraposée

   L'implication p → q est logiquement équivalente à sa contraposée ¬q → ¬p.
   Il est parfois plus facile de prouver la contraposée. En LEAN, on utilise
   `On contrapose`, qui transforme le but p → q en ¬q → ¬p.
-/

Exemple "Si n ≥ 3, alors n ≠ 0"
  Données : (n : ℕ)
  Hypothèses :
  Conclusion : n ≥ 3 → n ≠ 0
Démonstration :
  On contrapose
  Supposons h : n = 0 -- ¬(n ≠ 0) devient n = 0
  Montrons que n < 3 -- le but ¬(n ≥ 3) devient n < 3
  Calc n = 0 par h
     _ < 3 par calcul
QED


/- À vos ordinateurs : Completer la preuve suivante en utilisant sa contraposée.

-/
Exemple "Si n n'est pas divisible par 2, alors n n'est pas divisible par 4 (version contraposée)"
  Données : (n : ℕ)
  Hypothèses :
  Conclusion : (∀ k : ℕ, n ≠ k*2) → (∀ k' : ℕ, n ≠ k'*4)
Démonstration :
  sorry
QED

/- 6. Preuve par contradiction (raisonnement par l'absurde)

   Pour démontrer P, on suppose ¬P et on en déduit une impossibilité (Faux). En LEAN :
   `Supposons par l'absurde h : ¬P` transforme le but en `False`, avec `h : ¬P`
   dans le contexte.
-/

Exemple "Échanger l'ordre des quantificateurs peut rendre un énoncé faux"
  Données :
  Hypothèses :
  Conclusion : ¬ (∃ y : ℤ, ∀ x : ℤ, y > x) -- On veut démontrer que la negation de cet ennoncée est vraie
Démonstration :
  Supposons par l'absurde h : ∃ y : ℤ, ∀ x : ℤ, y > x
  Par h on obtient (y : ℤ) tel que (hy : ∀ x : ℤ, y > x)
  Par hy appliqué à y on obtient hy' : y > y
  On conclut par hy' -- hy' : y > y est absurde, `On conclut` le détecte directement
QED

/- À vos ordinateurs : Completer la preuve suivante par l'absurde -/

Exemple "Preuve par contradiction"
  Données : (x : ℝ) (y : ℝ)
  Hypothèses : (hxy : x ≠ y) (hx : x> 0) (hy : y> 0)
  Conclusion : x/y + y/x > 2
Démonstration :
  sorry
QED

/- 7. Preuve par disjonction de cas

   Lorsque les hypothèses se séparent naturellement en plusieurs cas qui couvrent toutes les possibilités, on traite chaque cas séparément avec
   `On discute en utilisant h`, où `h : P ∨ Q`.
-/

Exemple "n(n+1) est toujours pair"
  Données : (n : ℤ)
  Hypothèses : (parité : (∃ k : ℤ, n = 2*k) ∨ (∃ k : ℤ, n = 2*k+1)) -- on admet que tout entier est pair ou impair
  Conclusion : ∃ k : ℤ, n*(n+1) = 2*k
Démonstration :
  On discute en utilisant parité
  Supposons hp : ∃ k : ℤ, n = 2*k
  Par hp on obtient (k : ℤ) tel que (hk : n = 2*k)
  Montrons que k*(n+1) convient
  Calc n*(n+1) = 2*k*(n+1)   par hk
       _       = 2*(k*(n+1)) par calcul
  Supposons hi : ∃ k : ℤ, n = 2*k+1
  Par hi on obtient (k : ℤ) tel que (hk : n = 2*k+1)
  Montrons que (2*k+1)*(k+1) convient
  Calc n*(n+1) = (2*k+1)*(n+1)      par hk
       _       = (2*k+1)*(2*k+1+1) par hk
       _       = 2*((2*k+1)*(k+1)) par calcul
QED

/- À vos ordinateurs: Formaliser l'excercice 2.33 de la séance d'excercises (difficile)
 -/
Exemple "Exercice 2.33"
  Données : (n : ℤ)
  Hypothèses : -- Discuter selon n mod 3
  Conclusion : ∃ k : ℤ, n*(n+1)*(n+2) = 6*k
Démonstration :
  sorry
QED


-- #############################


/- 8. Preuves d'existence et d'unicité

   Un énoncé ∃! x, P(x) contient deux affirmations : l'EXISTENCE d'un tel x,
   et son UNICITÉ (deux objets qui vérifient P sont forcément égaux). On les
   prouve toujours séparément — c'est ce qu'on fait ci-dessous en deux
   exemples plutôt qu'en un seul, pour bien voir les deux étapes.
-/

Exemple "Existence d'une solution à x + 3 = a"
  Données : (a : ℝ)
  Hypothèses :
  Conclusion : ∃ x : ℝ, x + 3 = a
Démonstration :
  Montrons que a - 3 convient
  On calcule
QED

Exemple "Unicité de la solution à x + 3 = a"
  Données : (a x y : ℝ)
  Hypothèses : (hx : x + 3 = a) (hy : y + 3 = a)
  Conclusion : x = y
Démonstration :
  Calc x = a - 3 par hx
     _   = y     par hy
QED


/- 9. Le principe des tiroirs (pigeonhole)

   Si N objets sont répartis dans n tiroirs et que N > n, alors au moins un
   tiroir contient au moins deux objets. C'est un argument de comptage, pas
   un calcul symbolique : on ne le formalise pas en LEAN dans ce cours, mais
   c'est un outil puissant (voir l'exercice sur les anniversaires plus bas).
-/


/- Exercices -/

/- Exercice 2.31 : prouver par contraposée que si 3n+2 est pair, alors n est pair. -/
Exemple "Exercice 2.31"
  Données : (n : ℤ)
  Hypothèses :
  Conclusion : (∃ k : ℤ, 3*n + 2 = 2*k) → (∃ k' : ℤ, n = 2*k')
Démonstration :
  sorry
QED

/- Exercice 2.30 : prouver l'équivalence (indiquer clairement les deux directions). -/
Exemple "Exercice 2.30"
  Données : (n : ℤ)
  Hypothèses :
  Conclusion : (∃ k : ℤ, n = 2*k+1) ↔ (∃ k' : ℤ, n^2 = 2*k'+1)
Démonstration :
  sorry
QED


/- Exercice 2.35 : combinaison linéaire de diviseurs. -/
Exemple "Exercice 2.35"
  Données : (d a b : ℤ)
  Hypothèses : (hda : d ∣ a) (hdb : d ∣ b)
  Conclusion : ∀ u v : ℤ, d ∣ (a*u + b*v)
Démonstration :
  sorry
QED


/-
Note : aujourd'hui, on a couvert la plupart des techniques de preuve du
chapitre 2. Il en reste la preuve par récurrence, qui demande son propre cours dédié aux entiers naturels.
-/
