module zebra-puzzle where

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _∧_
  
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x
 
cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

replace : {A B : Set} {x y : A} {z : B} → (f : A → B) → x ≡ y → f x ≡ z → f y ≡ z
replace f x≡y fx≡z = trans (sym (cong f x≡y)) fx≡z

infixr 9 _∘_
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)
  
record Iso (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : (x : A) → (from ∘ to) x ≡ x
    to∘from : (x : B) → (to ∘ from) x ≡ x

open Iso

transpose : {A B : Set} → Iso A B → Iso B A
transpose iso = record {to = from iso; from = to iso; from∘to = to∘from iso; to∘from = from∘to iso}

infixr 9 _⋆_
_⋆_ : {A B C : Set} → Iso B C → Iso A B → Iso A C
_⋆_ {A} {B} {C} f g = record {to = to'; from = from'; from∘to = from∘to'; to∘from = to∘from'}
  where
    to' = to f ∘ to g
    from' = from g ∘ from f
    from∘to' : (x : A) → (from g ∘ from f ∘ to f ∘ to g) x ≡ x
    from∘to' x with cong (from g) (from∘to f (to g x)) | from∘to g x
    ...           | lemma1 | lemma2 = trans lemma1 lemma2
    to∘from' : (x : C) → (to f ∘ to g ∘ from g ∘ from f) x ≡ x
    to∘from' x with cong (to f) (to∘from g (from f x)) | to∘from f x
    ...           | lemma1 | lemma2 = trans lemma1 lemma2
 
cong-to : {A B : Set} {x : B} {y : A} (iso : Iso A B) → from iso x ≡ y → x ≡ to iso y
cong-to {A} {B} {x} {y} iso eq with to∘from iso x | cong (to iso) eq
...                               | eq1           | eq2 = trans (sym eq1) eq2

cong-from : {A B : Set} {x : A} {y : B} (iso : Iso A B) → to iso x ≡ y → x ≡ from iso y
cong-from {A} {B} {x} {y} iso eq with from∘to iso x | cong (from iso) eq
...                                 | eq1           | eq2 = trans (sym eq1) eq2

elim-to : {A B : Set} {x y : A} (iso : Iso A B) → to iso x ≡ to iso y → x ≡ y
elim-to {A} {B} {x} {y} iso eq with from∘to iso x | from∘to iso y | cong (from iso) eq
...                               | eq1           | eq2           | eq3 = trans (trans (sym eq1) eq3) eq2

converse-to : {A B C : Set} (iso₁ : Iso A B) (iso₂ : Iso A C) {y₁ : B} {y₂ : C} → (∀ x → to iso₁ x ≡ y₁ → to iso₂ x ≡ y₂) → (∀ x → to iso₂ x ≡ y₂ → to iso₁ x ≡ y₁)
converse-to {A} {B} {C} iso₁ iso₂ {y₁} {y₂} f x eq = (sym ∘ cong-to iso₁) (trans eq1 eq2)
  where
    t : A
    t = from iso₁ y₁
  
    t-lemma : to iso₁ t ≡ y₁
    t-lemma = to∘from iso₁ y₁
  
    eq1 : t ≡ from iso₂ y₂
    eq1 = cong-from iso₂ (f t t-lemma)
    
    eq2 : from iso₂ y₂ ≡ x
    eq2 = sym (cong-from iso₂ eq)

data House : Set where
  house1 : House
  house2 : House
  house3 : House
  house4 : House
  house5 : House

data Nation : Set where
  english   : Nation
  swedish   : Nation
  danish    : Nation
  norwegian : Nation
  german    : Nation

data Color : Set where
  red    : Color
  green  : Color 
  white  : Color
  yellow : Color
  blue   : Color

data Pet : Set where
  dog    : Pet
  bird   : Pet 
  cat    : Pet 
  horse  : Pet 
  fish   : Pet 

data Drink : Set where
  tea    : Drink
  coffee : Drink
  milk   : Drink
  beer   : Drink
  water  : Drink

data Smoke : Set where
  prince     : Smoke
  pallmall   : Smoke
  dunhill    : Smoke
  blend      : Smoke
  bluemaster : Smoke

record Solution : Set where
  field
    nation : Iso House Nation
    color  : Iso House Color
    pet    : Iso House Pet
    drink  : Iso House Drink
    smoke  : Iso House Smoke

open Solution {{...}}

data Neighbor : House → House → Set where
  neighbor1 : Neighbor house1 house2
  neighbor2 : Neighbor house2 house3
  neighbor3 : Neighbor house3 house4
  neighbor4 : Neighbor house4 house5

record Rules ⦃ Sol : Solution ⦄ : Set where
  field
    rule1  : (h : House) → to nation h ≡ english → to color h ≡ red
    rule2  : (h : House) → to nation h ≡ swedish → to pet h ≡ dog
    rule3  : (h : House) → to nation h ≡ danish → to drink h ≡ tea
    rule4  : (h₁ h₂ : House) → to color h₁ ≡ green → to color h₂ ≡ white → Neighbor h₁ h₂
    rule5  : (h : House) → to color h ≡ green → to drink h ≡ coffee
    rule6  : (h : House) → to smoke h ≡ pallmall → to pet h ≡ bird
    rule7  : (h : House) → to color h ≡ yellow → to smoke h ≡ dunhill
    rule8  : to drink house3 ≡ milk
    rule9  : to nation house1 ≡ norwegian
    rule10 : (h₁ h₂ : House) → to smoke h₁ ≡ blend → to pet h₂ ≡ cat → Neighbor h₁ h₂ ∨ Neighbor h₂ h₁
    rule11 : (h₁ h₂ : House) → to pet h₁ ≡ horse → to smoke h₂ ≡ dunhill → Neighbor h₁ h₂ ∨ Neighbor h₂ h₁
    rule12 : (h : House) → to smoke h ≡ bluemaster → to drink h ≡ beer
    rule13 : (h : House) → to nation h ≡ german → to smoke h ≡ prince
    rule14 : (h₁ h₂ : House) → to nation h₁ ≡ norwegian → to color h₂ ≡ blue → Neighbor h₁ h₂ ∨ Neighbor h₂ h₁
    rule15 : (h₁ h₂ : House) → to smoke h₁ ≡ blend → to drink h₂ ≡ water → Neighbor h₁ h₂ ∨ Neighbor h₂ h₁

open Rules {{...}}

theorem : ⦃ Sol : Solution ⦄ → ⦃ Rul : Rules ⦄ → (to pet house4 ≡ fish) ∧ (to nation house4 ≡ german)
theorem ⦃ Sol ⦄ ⦃ Rul ⦄ = lemma23 , lemma16
  where
    house-blue : House
    house-blue = from color blue
  
    house-blue-lemma : to color house-blue ≡ blue
    house-blue-lemma = to∘from color blue
  
    house-green : House
    house-green = from color green
  
    house-green-lemma : to color house-green ≡ green
    house-green-lemma = to∘from color green
  
    house-white : House
    house-white = from color white
  
    house-white-lemma : to color house-white ≡ white
    house-white-lemma = to∘from color white
  
    house-english : House
    house-english = from nation english
  
    house-english-lemma : to nation house-english ≡ english
    house-english-lemma = to∘from nation english
    
    house-horse : House
    house-horse = from pet horse
  
    house-horse-lemma : to pet house-horse ≡ horse
    house-horse-lemma = to∘from pet horse
    
    house-blend : House
    house-blend = from smoke blend

    house-blend-lemma : to smoke house-blend ≡ blend
    house-blend-lemma = to∘from smoke blend
  
    house-cat : House
    house-cat = from pet cat

    house-cat-lemma : to pet house-cat ≡ cat
    house-cat-lemma = to∘from pet cat
  
    lemma1-1 : (h : House) → to color h ≡ blue → h ≡ house2
    lemma1-1 h      p with rule14 house1 h rule9 p
    lemma1-1 house2 p    | left neighbor1 = refl
    
    lemma1 : to color house2 ≡ blue
    lemma1 = let lemma = lemma1-1 house-blue house-blue-lemma
             in  sym (cong-to color lemma)
  
    lemma2-1 : Neighbor house-green house-white
    lemma2-1 = rule4 house-green house-white house-green-lemma house-white-lemma
      
    lemma2-2 : {A : Set} → to color house2 ≡ white → A
    lemma2-2 eq with trans (sym eq) lemma1
    ...             | ()
  
    lemma2-3 : {A : Set} → to color house2 ≡ green → A
    lemma2-3 eq with trans (sym eq) lemma1
    ...             | ()
    
    lemma2-4 : {A : Set} → to drink house3 ≡ coffee → A
    lemma2-4 eq with trans (sym eq) rule8
    ...            | ()
  
    lemma2-5 : (to color house4 ≡ green) ∧ (to color house5 ≡ white)
    lemma2-5 with house-green | house-white | lemma2-1  | house-green-lemma | house-white-lemma | rule5 house-green house-green-lemma
    ...         | house1      | house2      | neighbor1 | _ | lemma | _ = lemma2-2 lemma
    ...         | house2      | house3      | neighbor2 | lemma | _ | _ = lemma2-3 lemma
    ...         | house3      | house4      | neighbor3 | _ | _ | lemma = lemma2-4 lemma
    ...         | house4      | house5      | neighbor4 | lemma1 | lemma2 | _ = lemma1 , lemma2
    
    lemma2 : to color house4 ≡ green
    lemma2 = fst lemma2-5
  
    lemma3 : to color house5 ≡ white
    lemma3 = snd lemma2-5
  
    lemma4 : to drink house4 ≡ coffee
    lemma4 = rule5 house4 lemma2
    
    lemma5-1 : {A : Set} → to nation house1 ≡ english → A
    lemma5-1 eq with trans (sym eq) rule9
    ...            | ()
  
    lemma5-2 : house-english ≡ from color red
    lemma5-2 = cong-from color (rule1 house-english house-english-lemma)
    
    lemma5-3 : to color house1 ≡ red → to nation house1 ≡ english
    lemma5-3 eq = let x : from color red ≡ house1
                      x = sym (cong-from color eq)
                  in sym (cong-to nation (trans lemma5-2 x))
    
    lemma5-4 : {A : Set} → to color house1 ≡ green → A
    lemma5-4 eq with trans (cong-from color eq) (sym (cong-from color lemma2))
    ...            | ()
  
    lemma5-5 : {A : Set} → to color house1 ≡ white → A
    lemma5-5 eq with trans (cong-from color eq) (sym (cong-from color lemma3))
    ...            | ()
    
    lemma5-6 : {A : Set} → to color house1 ≡ blue → A
    lemma5-6 eq with trans (cong-from color eq) (sym (cong-from color lemma1))
    ...            | ()
  
    lemma5 : to color house1 ≡ yellow
    lemma5 with to color house1 | lemma5-3 | lemma5-4 | lemma5-5 | lemma5-6
    ...       | red    | lemma | _ | _ | _ = lemma5-1 (lemma refl)
    ...       | green  | _ | lemma | _ | _ = lemma refl
    ...       | white  | _ | _ | lemma | _ = lemma refl
    ...       | yellow | _ | _ | _ | _ = refl
    ...       | blue   | _ | _ | _ | lemma = lemma refl
    
    lemma6-1 : {A : Set} → to color house3 ≡ green → A
    lemma6-1 eq with elim-to color (trans eq (sym lemma2))
    ...            | ()
    
    lemma6-2 : {A : Set} → to color house3 ≡ white → A
    lemma6-2 eq with elim-to color (trans eq (sym lemma3))
    ...            | ()
  
    lemma6-3 : {A : Set} → to color house3 ≡ yellow → A
    lemma6-3 eq with elim-to color (trans eq (sym lemma5))
    ...            | ()
  
    lemma6-4 : {A : Set} → to color house3 ≡ blue → A
    lemma6-4 eq with elim-to color (trans eq (sym lemma1))
    ...            | ()
  
    lemma6 : to color house3 ≡ red
    lemma6 with to color house3 | lemma6-1 | lemma6-2 | lemma6-3 | lemma6-4
    ...       | red    | _ | _ | _ | _ = refl
    ...       | green  | lemma | _ | _ | _ = lemma refl
    ...       | white  | _ | lemma | _ | _ = lemma refl
    ...       | yellow | _ | _ | lemma | _ = lemma refl
    ...       | blue   | _ | _ | _ | lemma = lemma refl
  
    lemma7-1 : house-english ≡ house3
    lemma7-1 = trans lemma5-2 (sym (cong-from color lemma6))
    
    lemma7 : to nation house3 ≡ english
    lemma7 = sym (cong-to nation lemma7-1)
  
    lemma8 : to smoke house1 ≡ dunhill
    lemma8 = rule7 house1 lemma5
  
    lemma9 : to pet house2 ≡ horse
    lemma9 with house-horse | house-horse-lemma | rule11 house-horse house1 house-horse-lemma lemma8
    ...       | house2      | eq                | right neighbor1 = eq
    
    lemma10-1 : {A : Set} → to drink house1 ≡ tea → A
    lemma10-1 eq with trans (sym rule9) (converse-to nation drink rule3 house1 eq)
    ...             | ()
  
    lemma10-2 : {A : Set} → to drink house1 ≡ coffee → A
    lemma10-2 eq with elim-to drink (trans eq (sym lemma4))
    ...             | ()
    
    lemma10-3 : {A : Set} → to drink house1 ≡ milk → A
    lemma10-3 eq with elim-to drink (trans eq (sym rule8))
    ...             | ()
    
    lemma10-4 : {A : Set} → to drink house1 ≡ beer → A
    lemma10-4 eq with trans (sym lemma8) (converse-to smoke drink rule12 house1 eq)
    ...             | ()
  
    lemma10 : to drink house1 ≡ water
    lemma10 with to drink house1 | lemma10-1 | lemma10-2 | lemma10-3 | lemma10-4
    ...        | tea    | lemma | _ | _ | _ = lemma refl
    ...        | coffee | _ | lemma | _ | _ = lemma refl
    ...        | milk   | _ | _ | lemma | _ = lemma refl
    ...        | beer   | _ | _ | _ | lemma = lemma refl
    ...        | water  | _ | _ | _ | _ = refl

    lemma11 : to smoke house2 ≡ blend
    lemma11 with house-blend | house-blend-lemma | rule15 house-blend house1 house-blend-lemma lemma10
    ...        | house2      | eq                | right neighbor1 = eq

    lemma12-1 : {A : Set} → to drink house2 ≡ coffee → A
    lemma12-1 eq with elim-to drink (trans eq (sym lemma4))
    ...             | ()

    lemma12-2 : {A : Set} → to drink house2 ≡ milk → A
    lemma12-2 eq with elim-to drink (trans eq (sym rule8))
    ...             | ()

    lemma12-3 : {A : Set} → to drink house2 ≡ beer → A
    lemma12-3 eq with trans (sym lemma11) (converse-to smoke drink rule12 house2 eq)
    ...             | ()

    lemma12-4 : {A : Set} → to drink house2 ≡ water → A
    lemma12-4 eq with elim-to drink (trans eq (sym lemma10))
    ...             | ()

    lemma12 : to drink house2 ≡ tea
    lemma12 with to drink house2 | lemma12-1 | lemma12-2 | lemma12-3 | lemma12-4
    ...        | tea    | _ | _ | _ | _ = refl
    ...        | coffee | lemma | _ | _ | _ = lemma refl
    ...        | milk   | _ | lemma | _ | _ = lemma refl
    ...        | beer   | _ | _ | lemma | _ = lemma refl
    ...        | water  | _ | _ | _ | lemma = lemma refl

    lemma13 : to nation house2 ≡ danish
    lemma13 = converse-to nation drink rule3 house2 lemma12

    lemma14-1 : {A : Set} → to drink house5 ≡ tea → A
    lemma14-1 eq with elim-to drink (trans eq (sym lemma12))
    ...             | ()

    lemma14-2 : {A : Set} → to drink house5 ≡ coffee → A
    lemma14-2 eq with elim-to drink (trans eq (sym lemma4))
    ...             | ()

    lemma14-3 : {A : Set} → to drink house5 ≡ milk → A
    lemma14-3 eq with elim-to drink (trans eq (sym rule8))
    ...             | ()

    lemma14-4 : {A : Set} → to drink house5 ≡ water → A
    lemma14-4 eq with elim-to drink (trans eq (sym lemma10))
    ...             | ()
    
    lemma14 : to drink house5 ≡ beer
    lemma14 with to drink house5 | lemma14-1 | lemma14-2 | lemma14-3 | lemma14-4
    ...        | tea    | lemma | _ | _ | _ = lemma refl
    ...        | coffee | _ | lemma | _ | _ = lemma refl
    ...        | milk   | _ | _ | lemma | _ = lemma refl
    ...        | beer   | _ | _ | _ | _ = refl
    ...        | water  | _ | _ | _ | lemma = lemma refl

    lemma15 : to smoke house5 ≡ bluemaster
    lemma15 = converse-to smoke drink rule12 house5 lemma14

    lemma16-1 : {A : Set} → to nation house4 ≡ english → A
    lemma16-1 eq with elim-to nation (trans eq (sym lemma7))
    ...             | ()
  
    lemma16-2 : {A : Set} → to nation house4 ≡ swedish → A
    lemma16-2 {A} eq = goal
      where
        lemma16-2-1-1 : {A : Set} → to nation house5 ≡ english → A
        lemma16-2-1-1 eq' with elim-to nation (trans eq' (sym lemma7))
        ...                 | ()

        lemma16-2-1-2 : {A : Set} → to nation house5 ≡ swedish → A
        lemma16-2-1-2 eq' with elim-to nation (trans eq' (sym eq))
        ...                  | ()
  
        lemma16-2-1-3 : {A : Set} → to nation house5 ≡ danish → A
        lemma16-2-1-3 eq' with elim-to nation (trans eq' (sym lemma13))
        ...                  |  ()
  
        lemma16-2-1-4 : {A : Set} → to nation house5 ≡ norwegian → A
        lemma16-2-1-4 eq' with elim-to nation (trans eq' (sym rule9))
        ...                  | ()
  
        lemma16-2-1 : to nation house5 ≡ german
        lemma16-2-1 with to nation house5 | lemma16-2-1-1 | lemma16-2-1-2 | lemma16-2-1-3 | lemma16-2-1-4
        ...            | english   | lemma | _ | _ | _ = lemma refl
        ...            | swedish   | _ | lemma | _ | _ = lemma refl
        ...            | danish    | _ | _ | lemma | _ = lemma refl
        ...            | norwegian | _ | _ | _ | lemma = lemma refl
        ...            | german    | _ | _ | _ | _ = refl
  
        lemma16-2-2 : to smoke house5 ≡ prince
        lemma16-2-2 = rule13 house5 lemma16-2-1

        goal : A
        goal with trans (sym lemma15) lemma16-2-2
        ...     | ()
  
    lemma16-3 : {A : Set} → to nation house4 ≡ danish → A
    lemma16-3 eq with elim-to nation (trans eq (sym lemma13))
    ...             | ()
  
    lemma16-4 : {A : Set} → to nation house4 ≡ norwegian → A
    lemma16-4 eq with elim-to nation (trans eq (sym rule9))
    ...             | ()
  
    lemma16 : to nation house4 ≡ german
    lemma16 with to nation house4 | lemma16-1 | lemma16-2 | lemma16-3 | lemma16-4
    ...        | english   | lemma | _ | _ | _ = lemma refl
    ...        | swedish   | _ | lemma | _ | _ = lemma refl
    ...        | danish    | _ | _ | lemma | _ = lemma refl
    ...        | norwegian | _ | _ | _ | lemma = lemma refl
    ...        | german    | _ | _ | _ | _ = refl

    lemma17 : to smoke house4 ≡ prince
    lemma17 = rule13 house4 lemma16
  
    lemma18-1 : {A : Set} → to nation house5 ≡ english → A
    lemma18-1 eq with elim-to nation (trans eq (sym lemma7))
    ...             | ()

    lemma18-2 : {A : Set} → to nation house5 ≡ danish → A
    lemma18-2 eq with elim-to nation (trans eq (sym lemma13))
    ...             | ()

    lemma18-3 : {A : Set} → to nation house5 ≡ norwegian → A
    lemma18-3 eq with elim-to nation (trans eq (sym rule9))
    ...             | ()

    lemma18-4 : {A : Set} → to nation house5 ≡ german → A
    lemma18-4 eq with elim-to nation (trans eq (sym lemma16))
    ...              | ()
  
    lemma18 : to nation house5 ≡ swedish
    lemma18 with to nation house5 | lemma18-1 | lemma18-2 | lemma18-3 | lemma18-4
    ...        | english   | lemma | _ | _ | _ = lemma refl 
    ...        | swedish   | _ | _ | _ | _ = refl 
    ...        | danish    | _ | lemma | _ | _ = lemma refl 
    ...        | norwegian | _ | _ | lemma | _ = lemma refl 
    ...        | german    | _ | _ | _ | lemma = lemma refl 

    lemma19-1 : {A : Set} → to smoke house3 ≡ prince → A
    lemma19-1 eq with elim-to smoke (trans eq (sym lemma17))
    ...             | ()

    lemma19-2 : {A : Set} → to smoke house3 ≡ dunhill → A
    lemma19-2 eq with elim-to smoke (trans eq (sym lemma8))
    ...             | ()

    lemma19-3 : {A : Set} → to smoke house3 ≡ blend → A
    lemma19-3 eq with elim-to smoke (trans eq (sym lemma11))
    ...             | ()

    lemma19-4 : {A : Set} → to smoke house3 ≡ bluemaster → A
    lemma19-4 eq with elim-to smoke (trans eq (sym lemma15))
    ...             | ()

    lemma19 : to smoke house3 ≡ pallmall
    lemma19 with to smoke house3 | lemma19-1 | lemma19-2 | lemma19-3 | lemma19-4
    ...        | prince     | lemma | _ | _ | _ = lemma refl 
    ...        | pallmall   | _ | _ | _ | _ = refl 
    ...        | dunhill    | _ | lemma | _ | _ = lemma refl 
    ...        | blend      | _ | _ | lemma | _ = lemma refl 
    ...        | bluemaster | _ | _ | _ | lemma = lemma refl 

    lemma20 : to pet house3 ≡ bird
    lemma20 = rule6 house3 lemma19

    lemma21 : to pet house5 ≡ dog
    lemma21 = rule2 house5 lemma18
    
    lemma22-1 : {A : Set} → to pet house3 ≡ cat → A
    lemma22-1 eq with trans (sym eq) lemma20
    ...             | ()
  
    lemma22 : to pet house1 ≡ cat
    lemma22 with house-cat | house-cat-lemma | rule10 house2 house-cat lemma11 house-cat-lemma
    ...        | house3    | lemma | left  neighbor2 = lemma22-1 lemma
    ...        | house1    | lemma | right neighbor1 = lemma

    lemma23-1 : {A : Set} → to pet house4 ≡ dog → A
    lemma23-1 eq with elim-to pet (trans eq (sym lemma21))
    ...             | ()
  
    lemma23-2 : {A : Set} → to pet house4 ≡ bird → A
    lemma23-2 eq with elim-to pet (trans eq (sym lemma20))
    ...             | ()
  
    lemma23-3 : {A : Set} → to pet house4 ≡ cat → A
    lemma23-3 eq with elim-to pet (trans eq (sym lemma22))
    ...             | ()
  
    lemma23-4 : {A : Set} → to pet house4 ≡ horse → A
    lemma23-4 eq with elim-to pet (trans eq (sym lemma9))
    ...             | ()
  
    lemma23 : to pet house4 ≡ fish
    lemma23 with to pet house4 | lemma23-1 | lemma23-2 | lemma23-3 | lemma23-4
    ...        | dog   | lemma | _ | _ | _ = lemma refl 
    ...        | bird  | _ | lemma | _ | _ = lemma refl 
    ...        | cat   | _ | _ | lemma | _ = lemma refl 
    ...        | horse | _ | _ | _ | lemma = lemma refl 
    ...        | fish  | _ | _ | _ | _ = refl 
