import Verbose.French.ExampleLib
import MAT120.src.lois_logique
import MAT120.src.calcul
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

#check (2=3 : Prop)
#check ((∃ x : ℕ, x = 1/2) : Prop) -- Dans ce contexte, pour LEAN a/b est le résultat de la division euclidienne de a par b
example: (1: ℕ)/2 = 0 := by simp -- LEAN a accepté ma preuve du fait que 1/2 : ℕ est égal à 0.
example: (1: ℝ)/2 ≠ 0 := by simp
#check (√2 : ℕ)

-- COMMENTAIRES

/- Voici un commentaire en block
   Vous pouvez écrire plusieurs lignes dedans!
-/
-- Voici un commentaire de ligne

Exemple "Démontrer que les deux énoncés sont équivalents en utilisant seulement les règles LP_1 à LP_21"
  Données : (A B : Prop)
  Hypothèses :
  Conclusion : (A ∨ (A ∧ B)) ↔ A
Démonstration :
On réécrit via LP_12
-- Cette technique nous permet de réécrire une proposition avec une autre proposition équivalente.
sorry
QED

/- Les priorités des opérations en LEAN et parenthèses -/

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

/- Exercice : Formaliser l'énoncé 1-c) du fichier lab_4.pdf dans un bloc VerboseLEAN -/

Exemple "Exercice 1-c)"
Données : (A B : Prop)
  Hypothèses :
  Conclusion : ¬(A → B) ↔ A ∧ ¬B
Démonstration :
On réécrit via LP_22
On réécrit via LP_18
On réécrit via LP_21
QED

--- 30 min

-- #####################################################################
/- Techniques de démonstration -/

/- 1. Preuve directe: partir des définitions

   Avant de prouver quoi que ce soit, il faut toujours revenir aux définitions :
     - n est pair s'il existe k ∈ ℤ tel que n = 2k.
     - n est impair s'il existe k ∈ ℤ tel que n = 2k + 1.
     - a divise b (noté a ∣ b) s'il existe k ∈ ℤ tel que b = ak.
   En LEAN, `a ∣ b` est déjà une notation pour `∃ k, b = a*k` (le symbole `∣` s'écrit \dvd)
-/

Exemple "3 divise 12"
  Données :
  Hypothèses :
  Conclusion : (3 : ℕ) ∣ 12 -- Signification ∃ k : ℤ, 12 = 3*k
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

/- À vos ordinateurs : Formaliser la preuve détaillée de l'exercice 2.29
-/

Exemple "Prouver directement que le produit de deux entiers impairs est impair"
  Données: (n : ℤ) (m : ℤ)
  Hypothèses: (hn : ∃ k : ℤ , n=2*k +1) (hm : ∃ k : ℤ , m=2*k +1)
  Conclusion: ∃ k : ℤ, n*m = 2*k +1
Démonstration:
  Par hn on obtient (k: ℤ) tel que (hnk : n = 2*k +1)
  Par hm on obtient (k': ℤ) tel que (hmk : m = 2*k'+1)
  Montrons que 2*k*k'+ k +k' convient
  Calc n*m = (2*k+1)* m par hnk
      _ = (2*k +1)*(2*k'+1) par hmk
      _ = 2*2*k*k' + 2*k + 2*k' +1 par calcul
      _ = 2*(2*k*k' + k +k') +1 par calcul
QED

-- Fin de la première heure, PAUSE

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


/- À vos ordinateurs : Formaliser la preuve détaillée de l'exercice 2.30

Exemple "Prouver que pour tout n : ℤ, n est impair si et seulement si n^2 est impair"
  Données:
  Hypothèses:
  Conclusion:
Démonstration:
QED

Q: Quelle technique de démonstration devez-vous connaître pour démontrer que si n^2 est pair, alors n est pair?
-/

Exemple "Prouver que pour tout n : ℤ, n est impair si et seulement si n^2 est impair"
  Données: -- (n: ℤ)
  Hypothèses:
  Conclusion: ∀ n : ℤ, (∃ k : ℤ, n = 2*k +1 ) ↔ (∃ k' : ℤ , n^2 = 2*k' +1 )
Démonstration:
Soit (n : ℤ)
Montrons d'abord que (∃ k : ℤ, n = 2*k +1 ) → (∃ k' : ℤ, n^2 = 2*k'+1)
Supposons hn : ∃ k : ℤ, n = 2*k +1
Par hn on obtient k tel que hnk : n = 2*k+1
Montrons que (2*k^2 + 2*k) convient
Calc n^2 = (2*k+1)^2 par hnk
    _ = 4*k^2+4*k+1 par calcul
    _ = 2*(2*k^2+2*k) +1 par calcul
Montrons maintenant que (∃ k' : ℤ, n^2 = 2*k'+1) → (∃ k : ℤ, n = 2*k+1)
On contrapose
sorry
QED

--- 1h30

/- 3. Réfuter un énoncé : le contre-exemple

   Pour démontrer un énoncé universel ∀x P(x), un seul exemple ne suffit jamais. Mais pour le réfuter, un seul contre-exemple suffit. On combine
   `On pousse la négation` (¬∀ devient ∃¬) avec `Montrons que ... convient`.
-/

Exemple "Réfuter : a² = b² implique  a = b"
  Données :
  Hypothèses :
  Conclusion : ¬ (∀ a b : ℝ, a^2 = b^2 → a = b) -- Traduction:
Démonstration :
  On pousse la négation -- ¬(P → Q) ↔ ?
  Montrons que (1:ℝ) convient
  Montrons que (-1:ℝ) convient -- On obtient un énoncé de la forme P ∧ Q
  Montrons d'abord que (1:ℝ)^2 = (-1:ℝ)^2
  On calcule
  Montrons maintenant que (1:ℝ) ≠ (-1:ℝ)
  On calcule
QED


/- À vos ordinateurs : Formaliser et donner un contre-exemple de l'énoncé de l'exercice 1.17 c)

Exemple "Exercice 1.17 c)"
  Données:
  Hypothèses:
  Conclusion:
Démonstration:
sorry
QED
-/

Exemple "Exercice_1.17_c)"
  Données:
  Hypothèses:
  Conclusion: ¬ (∀ x : ℝ, x^2 ≥ x)
Démonstration:
  On pousse la négation
  Montrons que (1: ℝ)/2 convient
  Calc (1/2)^2 = (1 : ℝ)/4 par calcul
    _ < 1/2 par calcul
QED


/- 4. Preuve d'une conjonction
  Dans l'exercice "Réfuter : a² = b² n'implique pas a = b", on a vu que pour démontrer un énoncé de la forme P ∧ Q, on utilise la commande  `Montrons d'abord que P`... `Montrons maintenant que Q`...
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

/- Utilisation d'une conjonction : si une de vos hypothèses est une conjonction, la commande pour l'utiliser est `Par (h : P ∧ Q), on obtient (hP : P) (hQ : Q) `-/

/- À vos ordinateurs : compléter la preuve suivante : -/

Exemple "Transitivité de la division"
  Données : (a b c : ℕ)
  Hypothèses : (habc : (a : ℕ) ∣ b ∧ (b : ℕ )∣ c) -- P ∧ Q
  Conclusion : (a ∣ c)
Démonstration :
  Par habc on obtient ha hb  -- Traduction:
  -- sorry
  Par ha on obtient k : ℕ tel que hk
  Par hb on obtient k' : ℕ tel que hk'
  Montrons que k*k' convient
  -- On calcule
  Calc c = b * k' par hk'
       _ = (a*k)*k' par hk
       _ = a*(k*k') par calcul -- Dernière fois qu'on peut voir le but original, c'est avant le `par`
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


/- À vos ordinateurs : Compléter la preuve suivante en utilisant sa contraposée.

-/
Exemple "Si n n'est pas divisible par 2, alors n n'est pas divisible par 4 (version contraposée)"
  Données : (n : ℕ)
  Hypothèses :
  Conclusion : (∀ k : ℕ, n ≠ k*2) → (∀ k' : ℕ, n ≠ k'*4)
Démonstration :
-- sorry
  On contrapose
  Supposons h : ∃ k' : ℕ, n = k'*4 -- LEAN nous montre directement l'énoncé « poussé » : ¬(∀ k', n ≠ k'*4) devient ∃ k', n = k'*4
  Par h on obtient (k' : ℕ) tel que (hk' : n = k'*4)
  Montrons que k'*2 convient
  Calc n = k'*4    par hk'
     _   = k'*2*2  par calcul
QED



/- 6. Preuve par contradiction (raisonnement par l'absurde)

   Pour démontrer P, on suppose ¬P et on en déduit une impossibilité (Faux). En LEAN :
   `Supposons par l'absurde h : ¬P` transforme le but en `False`, avec `h : ¬P`
   dans le contexte.
-/

Exemple "Échanger l'ordre des quantificateurs peut rendre un énoncé faux"
  Données :
  Hypothèses :
  Conclusion : (∀ y : ℤ, ∃ x : ℤ, y ≤ x) -- On veut démontrer que la négation de cet énoncé est vraie
Démonstration :
  Supposons par l'absurde h : ∃ y : ℤ, ∀ x : ℤ, y > x
  Par h on obtient (y : ℤ) tel que (hy : ∀ x : ℤ, y > x)
  Par hy appliqué à y on obtient hy' : y > y
  On conclut par hy' -- hy' : y > y est absurde, `On conclut` le détecte directement
QED

/- À vos ordinateurs : Compléter la preuve suivante par l'absurde
- Dans un bloc `Calc` on peut utiliser la commande `puisque` pour utiliser plusieurs énnoncés, dans ce cas, il faut écrire l'énnoncé au complet!
- Pour introduire un nouveau énnoncé, on écrit `Fait nom: énnoncé` + `car` + preuve de l'énnoncé
 -/

Exemple "Combinaison de deux majorations"
  Données : (x y : ℝ)
  Hypothèses : (h1 : x + y ≥ 10) (h2 : x ≤ 4)
  Conclusion : y > 5
Démonstration :
  Supposons par l'absurde h : y ≤ 5
  Fait contra : (10:ℝ) ≤ 9 car
    Calc (10:ℝ) ≤ x + y par h1
     _ ≤ 4 + 5 puisque x ≤ 4 et y ≤ 5
     _ = 9 par calcul
  On conclut par contra
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

/- À vos ordinateurs : Formaliser l'exercice 2.33 de la séance d'exercices (difficile)
 -/
Exemple "Exercice 2.33"
  Données : (n : ℤ)
  Hypothèses : -- Discuter selon n mod 3
  Conclusion : ∃ k : ℤ, n*(n+1)*(n+2) = 6*k
Démonstration :
  sorry
QED



--- Pour voir toutes ce qui est possible de démontrer avec VerboseLEAN, voir : https://www.imo.universite-paris-saclay.fr/~patrick.massot/mdd154/reference.pdf
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
