import Verbose.French.ExampleLib
import MAT120.src.lois_logique

open Verbose.French
open Verbose.Named

/- Plan de la séance
- Syntax de base (∨ ∧ ¬ → ↔)
- Les ensembles de nombres, ℕ ℝ ℚ ℤ ≠ = etc
- Les quantificateurs ∃ ∀ (syntax)
- La syntaxe d'un exercice
- LEAN infoview
- `sorry` — la preuve par excuse
- Comment Lean place ses parenthèses

-/


/- 1. Syntaxe de base des connecteurs

   Chaque symbole se tape avec une abréviation commençant par `\` :
     ∧  « et »          \and
     ∨  « ou »          \or
     ¬  « non »         \not
     →  « implique »    \to   (ou \imp)
     ↔  « équivaut à »  \iff

   Un énoncé qui est soit vrai soit faux est de type `Prop`.
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

example : (2 : ℕ) = 2 := by rfl
example : (2 : ℝ) ≠ 3 := by norm_num

#check (2 : ℝ)   -- on précise le type entre parenthèses


/- 3. Les quantificateurs

     ∀  « pour tout »   \forall
     ∃  « il existe »   \exists

   Syntaxe :  ∀ x : ℕ, ...    ∃ x : ℕ, ...
   La virgule sépare la variable de l'énoncé.
-/

example : ∀ n : ℕ, n = n := by
  Soit n : ℕ
  On calcule

example : ∃ n : ℕ, n = 3 := by
  Montrons que 3 convient
  On calcule

example : ∀ x : ℕ, ∃ y : ℕ, x ≤ y := by
  Soit x : ℕ
  Montrons que x convient
  On calcule


/- 4. La syntaxe d'un exercice

     Exemple "un titre"
       Données :    les objets : (P Q : Prop), (n : ℕ), ...
       Hypothèses : ce que l'on suppose : (h : P → Q) (hP : P)
       Conclusion : ce que l'on doit démontrer
     Démonstration :
       ... les étapes ...
     QED

   La section Hypothèses peut être vide. `QED` marque la fin.
-/

Exemple "Exemple de preuve dans un bloc VerboseLEAN"
  Données : (P Q : Prop)
  Hypothèses : (h : P → Q) (hP : P)
  Conclusion : Q
Démonstration :
  On conclut par h appliqué à hP
QED

Exemple "Une implication évidente"
  Données : (P : Prop)
  Hypothèses :
  Conclusion : P → P
Démonstration :
  Supposons hP : P
  On conclut par hP
QED


/- 5. Le panneau « Lean Infoview »

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


/- 6. `sorry` — la preuve par excuse

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


/- 7. Comment Lean place ses parenthèses

   Sans parenthèses, Lean les ajoute selon des priorités fixes,
   du plus « collant » au moins « collant » :
     ¬   puis   ∧   puis   ∨   puis   →   puis   ↔
   `→` s'associe à droite ; un quantificateur s'étend le plus loin possible.

   Ci-dessous les deux membres sont le même énoncé pour Lean (`Iff.rfl`) :
   seules les parenthèses changent.
-/

example (P Q : Prop)     : (¬ P ∧ Q)         ↔ ((¬ P) ∧ Q)            := Iff.rfl
example (P Q R : Prop)   : (P ∨ Q ∧ R)       ↔ (P ∨ (Q ∧ R))          := Iff.rfl
example (P Q R : Prop)   : (P ∧ Q → R)       ↔ ((P ∧ Q) → R)          := Iff.rfl
example (P Q R : Prop)   : (P → Q → R)       ↔ (P → (Q → R))          := Iff.rfl
example (P Q R : Prop)   : (P → Q ↔ R)       ↔ ((P → Q) ↔ R)          := Iff.rfl
example (P Q : ℕ → Prop) : (∀ x, P x ∧ Q x)  ↔ (∀ x, (P x ∧ Q x))     := Iff.rfl

/- Excercices -/

/- Démontrer en utilisant seulement les lois de LP-1 à LP-13-/
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

/- Ecrire sa contraposée-/

Exemple "Contraposée"
Données : (n : ℕ)
Hypothèses :
Conclusion : (∀ k : ℕ, n ≠ k*2) → (∀ k' : ℕ, n ≠ k'*4)
Démonstration :
  On contrapose
  sorry
QED

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
