import Verbose.French.ExampleLib
import MAT120.src.lois_logique

open Verbose.French
open Verbose.Named

/- Plan de la séance
- Syntax de base (∨ ∧ ¬ → ↔)
- Les ensembles de nombres, ℕ ℝ ℚ ℤ ≠ = etc
- La syntaxe d'un exercice
- LEAN infoview
- Les quantificateurs ∃ ∀ (syntax)
- `sorry` — la preuve par excuse
- Comment Lean place ses parenthèses

-/

/- LEAN est un **assistant de preuve par ordinateur**, c'est-à-dire qu'il permet à
l'usager de savoir si une **proposition** est vraie. Dans LEAN, il y a différents **types** d'objets, dont le plus important est le type Prop : -/

example (P : Prop) : Prop := P -- P est une proposition : un énoncé, ni vrai ni faux pour l'instant. On dit que P est un **terme** de `Prop`

/- Comme on l'a appris, une proposition peut avoir deux valeurs de vérité : Vrai ou Faux -/

example (P : Prop) (hP : P) : P := hP -- Ici, hP est un **terme** de P, ce qui pour LEAN veut dire que hP est une preuve que P est vraie

/- Dans les deux exemples précédents, on doit dire à LEAN qui sont P et hP. Ceci est déclaré entre `example` et `:`.

Après `:`, vient la *demande* : dans le premier exemple on demande à LEAN un exemple de proposition, et on lui donne (`:=`) P. Dans le deuxième exemple, on lui demande une preuve de P, et on lui donne (`:=`) hP. -/

-- Quelle est la signification de l'exemple suivant?

example (P : Prop) (nhP : ¬ P) : ¬ P := nhP

/- 1. Syntaxe de base des connecteurs

   Chaque symbole se tape avec une abréviation commençant par `\` :
     ∧  « et »          \and
     ∨  « ou »          \or
     ¬  « non »         \not
     →  « implique »    \to   (ou \imp)
     ↔  « équivaut à »  \iff
-/

example (P Q : Prop) : Prop := P ∧ Q
example (P Q : Prop) : Prop := P ∨ Q
example (P : Prop)   : Prop := ¬ P
example (P Q : Prop) : Prop := P → Q
example (P Q : Prop) : Prop := P ↔ Q


/- 2. Les ensembles de nombres

     ℕ  entiers naturels    \N
     ℤ  entiers relatifs    \Z
     ℚ  nombres rationnels   \Q
     ℝ  nombres réels        \R

   Égalité `=` ; différence `≠` (se tape \ne).
-/

example : ℕ := 42
example : ℤ := -7
example : ℝ := 3.5

example : (2 : ℕ) = 2 := by rfl -- Traduction:
example : (2 : ℝ) ≠ 3 := by norm_num -- Traduction:
#check (2 : ℝ)   -- on précise le type entre parenthèses

/- Dans les exemples précedents, `rfl` et `norm_num` sont des exemples de **techniques** de preuve.

D'après votre cours, quels exemples de techniques de preuve connaissez-vous?
R :=
-/

/- 3. La syntaxe d'un exercice avec VerboseLEAN

     Exemple "un titre"
       Données :    les objets : (P Q : Prop), (n : ℕ), ...
       Hypothèses : ce que l'on suppose : (h : P → Q) (hP : P)
       Conclusion : ce que l'on doit démontrer
     Démonstration :
       ... les étapes ...
     QED

   La section Hypothèses peut être vide. `QED` marque la fin.

-/

Exemple "Une implication évidente"
  Données : (P : Prop)
  Hypothèses :
  Conclusion : P → P
Démonstration :
  Supposons hP : P
  On conclut par hP
QED

Exemple "Exemple d'une preuve avec hypothèses"
  Données : (P Q : Prop) -- Traduction :
  Hypothèses : (h : P → Q) (hP : P) -- Traduction :
  Conclusion : Q
Démonstration :
  Par h il suffit de montrer que P -- Exemple de tactique, comparer avec l'exercice 1.23 b)
  On conclut par hP
QED

/- 4. Le panneau « Lean Infoview »

   En plaçant le curseur dans une preuve, le panneau de droite montre :
     - les objets et hypothèses disponibles (le contexte),
     - après `⊢`, le but : ce qu'il reste à démontrer.
   Le but change à chaque étape ; « No goals » = preuve finie.

   Soulignement rouge = erreur ; jaune = avertissement (souvent `sorry`).
-/

Exemple "Observer l'infoview"
  Données : (P Q : Prop)
  Hypothèses : (hP : P) (hQ : Q)
  Conclusion : P ∧ Q
Démonstration :
  Montrons d'abord que P
  On conclut par hP
  Montrons maintenant que Q
  On conclut par hQ
QED

Exemple "Une autre façon de prouver et utiliser une implication"
  Données : (P Q R: Prop) -- Traduction :
  Hypothèses : (h : R → P) (k : P → Q)
  Conclusion : R → Q
Démonstration :
  Supposons hR : R
  Par h appliqué à hR on obtient (hp : P) -- Ceci est une autre façon de rédiger la technique de preuve de l'implication.
  On conclut par k appliqué à hp
QED


/- Exemple de calcul propositionnel -/

Exemple "Laboratoire 4 1)"
  Données : (A B : Prop)
  Hypothèses :
  Conclusion : (A ∨ (A ∧ B)) ↔ A
Démonstration :
On réécrit via LP_12 -- Cette technique nous permet de réécrire une proposition avec une autre proposition équivalente.
On réécrit via LP_6
On réécrit via LP_11
On réécrit via LP_5
On réécrit via LP_14
QED

/- 5. `sorry` — la preuve par excuse

   `sorry` dit à Lean « fais-moi confiance » : la preuve est acceptée mais
   Lean affiche un avertissement jaune. Ce n'est pas une vraie preuve.
-/

Exemple "Preuve à compléter"
  Données : (P Q : Prop)
  Hypothèses : (h : P → Q) (hP : P)
  Conclusion : Q
Démonstration :
  sorry
QED

/- 6. Les quantificateurs

     ∀  « pour tout »   \forall
     ∃  « il existe »   \exists

   Syntaxe :  ∀ x : ℕ, ...    ∃ x : ℕ, ...
   La virgule sépare la variable de l'énoncé.
-/

Exemple "Pour tout n, n égale n"
  Données :
  Hypothèses :
  Conclusion : ∀ n : ℕ, n = n
Démonstration :
  Soit n : ℕ
  On calcule -- Cette technique nous permet de vérifier des égalités, ici clairement n = n, mais on doit le dire à LEAN !
QED

Exemple "Il existe n tel que n égale 3"
  Données :
  Hypothèses :
  Conclusion : ∃ n : ℕ, n = 3
Démonstration :
  Montrons que 3 convient
  On calcule
QED

/- À vous de jouer ! -/
Exemple "Pour tout x, il existe y plus grand"
  Données :
  Hypothèses :
  Conclusion : ∀ x : ℕ, ∃ y : ℕ, x ≤ y
Démonstration :
  sorry
QED

/- Bonus (si le temps le permet) : nier et ordonner les quantificateurs.
   ¬∀ devient ∃¬, et ¬∃ devient ∀¬ — la tactique `On pousse la négation`
   applique cette règle automatiquement. -/

Exemple "Nier un énoncé universel"
  Données :
  Hypothèses :
  Conclusion : ¬(∀ n : ℕ, n > 0)
Démonstration :
  On pousse la négation -- transforme le but en ∃ n : ℕ, n ≤ 0
  sorry
QED

/- L'ordre des quantificateurs compte : ∀x ∃y (y > x) est vraie, mais si on
   échange l'ordre, ∃y ∀x (y > x) devient fausse (aucun entier n'est plus
   grand que tous les entiers). On verra vendredi comment prouver qu'un
   énoncé est faux par contradiction ! -/

Exemple "L'ordre des quantificateurs compte"
  Données :
  Hypothèses :
  Conclusion : ∀ x : ℤ, ∃ y : ℤ, y > x
Démonstration :
  Soit x : ℤ
  Montrons que x + 1 convient
  On calcule
QED

/- Exemple : traduction de la Proposition 2.4 du cours -/

Exemple "Proposition 2.4"
  Données: (n : ℤ)
  Hypothèses:
  Conclusion: (∃ k : ℤ, n = 2*k) → (∃ k' :ℤ, n^2 = 2*k')
Démonstration:
 Supposons n_est_pair : (∃ k : ℤ, n = 2*k)
 Par n_est_pair on obtient k tel que (hn : n = 2*k) -- On doit toujours donner un nom à nos hypothèses en LEAN
 Montrons que 2*k^2 convient -- k' = 2*k^2
 -- On doit faire des calculs, ce qu'on indique par `Calc`
 Calc n^2 = (2*k)^2 par hn
      _ = 4*(k^2) par calcul
      _ = 2*(2*k^2) par calcul
QED


/- 7. Comment Lean place ses parenthèses

   Sans parenthèses, Lean les ajoute selon des priorités fixes,
   du plus « collant » au moins « collant » :
     ¬   puis   ∧   puis   ∨   puis   →   puis   ↔
   `→` s'associe à droite ; un quantificateur s'étend le plus loin possible.

   Ci-dessous les deux membres sont le même énoncé pour Lean une fois les
   parenthèses ajoutées ; c'est pourquoi la technique `Iff.rfl` suffit à
   conclure : seules les parenthèses changent.
-/

example (P Q : Prop)     : (¬ P ∧ Q)         ↔ ((¬ P) ∧ Q)            := Iff.rfl
example (P Q R : Prop)   : (P ∨ Q ∧ R)       ↔ (P ∨ (Q ∧ R))          := Iff.rfl
example (P Q R : Prop)   : (P ∧ Q → R)       ↔ ((P ∧ Q) → R)          := Iff.rfl
example (P Q R : Prop)   : (P → Q → R)       ↔ (P → (Q → R))          := Iff.rfl
example (P Q R : Prop)   : (P → Q ↔ R)       ↔ ((P → Q) ↔ R)          := Iff.rfl
example (P Q : ℕ → Prop) : (∀ x, P x ∧ Q x)  ↔ (∀ x, (P x ∧ Q x))     := Iff.rfl

/- Exercices -/

/- Formaliser et montrer les énoncés de l'exercice 1 du fichier Notes du cours/lab_4.pdf -/

Exemple "Laboratoire 4 : 1.b)"
  Données : (A B : Prop)
  Hypothèses :
  Conclusion : A
Démonstration :
sorry
QED

/- Compléter la preuve suivante -/

Exemple "Exercice 1.16"
  Données :
  Hypothèses :
  Conclusion :∃ n : ℕ , n^2 = 4
Démonstration :
sorry
QED


/-
Note : le but de ce cours est de vous présenter LEAN comme un outil d'apprentissage de la logique mathématique. LEAN est aussi utilisé de façon professionnelle par des mathématiciens et des informaticiens. Dans ce cours on utilise VerboseLEAN, une version de LEAN qui utilise le langage naturel (proche de ce que vous écririez dans vos notes par exemple). Par contre, la syntaxe « normale » de LEAN ressemble plus à un langage de programmation.
-/
