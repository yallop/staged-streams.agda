module streams where

open import Data.Unit using (⊤)
open import Data.Integer using (ℤ)
  renaming (_+_ to _+ᵢ_; _*_ to _*ᵢ_; _-_ to _-ᵢ_; +_ to int; _<_ to _<ᵢ_; _≤_ to _≤ᵢ_)
open import Data.Integer.DivMod using () renaming (_div_ to _/ᵢ_)
open import Data.Nat using (ℕ) renaming (_<_ to _<ₙ_)
import Data.Nat.Show
import Data.Nat.Properties
open import Data.String using (String; _++_) renaming (_==_ to _==ₛ_)
import Data.Char
import Data.Bool
open Data.Bool using () renaming (if_then_else_ to If_then_else_)
import Data.List
open import Data.Vec using (Vec) renaming (_∷_ to _∷ᵥ_; [] to []ᵥ)
open import Category.Monad.State using (State)
open import Data.Product hiding (map)
open import Function
open import Relation.Nullary.Decidable using (⌊_⌋)
import Data.Fin
open import Agda.Builtin.Equality

data c_type : Set where
  Void Char Int Bool : c_type
  Array : c_type → (n : ℕ) → c_type

record C : Set₁ where
  field
    Code : c_type → Set
    Ref : c_type → Set
    --_≃_ : ∀ { α β } → Code α → Code β → Set
    --_≤_ : Code Int → Code Int → Set
    ⟨_⟩ : ℤ → Code Int
    _+_ _*_ _-_ _/_ : Code Int → Code Int → Code Int
    _<_ _<=_ _>_ _>=_ _==_ : Code Int → Code Int → Code Bool
    true false : Code Bool
    _||_ _&&_ : Code Bool → Code Bool → Code Bool
    if_then_else_ : ∀ { α } → Code Bool → Code α → Code α → Code α
    [] : ∀ { α } → Code (Array α 0)
    _∷_ : ∀ { α n } → Code α → Code (Array α n) → Code (Array α (ℕ.suc n))
    _[_] : ∀ { α n } → Ref (Array α n) → (i : Code Int) → Ref α
    ★_ : ∀ { α } → Ref α → Code α
    _≔_ : ∀ { α } → Ref α → Code α → Code Void
    _；_ : ∀ { α β } → Code α → Code β → Code β
    decl : (α : c_type) → ∀ { β } → (Ref α → Code β) → Code β
    nop : Code Void
    for_to_then_ : (l : Code Int) → (u : Code Int) → (Ref Int → Code Void) → Code Void
    while_then_ : Code Bool → Code Void → Code Void

  infixr 0 _；_
  infix 1 if_then_else_
  infix 2 _≔_
  infix 3 _∷_
  infix 4 _/_
  infix 5 _*_
  infix 6 _+_
  infix 7 _-_
  infix 8 ★_ _||_ _&&_
  infix 9 _[_]

open C ⦃ ... ⦄

⟦_⟧ : c_type → Set
⟦ Void ⟧ = ⊤
⟦ Char ⟧ = Data.Char.Char
⟦ Int ⟧ = ℤ
⟦ Bool ⟧ = Data.Bool.Bool
⟦ Array α n ⟧ = Vec ⟦ α ⟧ n -- reversed order

-- Stream Fusion, to Completeness ----------------------------------------

data CardT : Set where
  atMost1 : CardT
  many : CardT

-- ProducerT (element type) (internal state) ⦃ implementation ⦄
data ProducerT (α σ : Set) ⦃ _ : C ⦄ : Set where
  -- for : (state → index) × (state → index → continuation → void)
  for : (σ → Code Int) × (σ → Code Int → (α → Code Void) → Code Void) → ProducerT α σ
  -- unfolder : (state → terminated?) × cardinality × (state → continuation → void)
  unfolder : (σ → Code Bool) × CardT × (σ → (α → Code Void) → Code Void) → ProducerT α σ

-- Producer (element type) ⦃ implementation ⦄
data Producer (α : Set) ⦃ _ : C ⦄ : Set₁ where
  -- producer : ⦃ internal state ⦄ → (initialisation function) × producer
  producer : ∀ { σ } → (∀ { ω } → (σ → Code ω) → Code ω) × (ProducerT α σ) → Producer α

-- Stream (element type) ⦃ implementation ⦄
data SStream (α : Set) ⦃ _ : C ⦄ : Set₁ where
  -- linear : producer of code elements
  linear : Producer α → SStream α
  -- nested : ⦃ stream code ⦄ → (producer of stream code) × (stream code → stream)
  nested : ∀ { β } → Producer β × (β → SStream α) → SStream α

Stream : ∀ ⦃ _ : C ⦄ → c_type → Set₁
Stream α = SStream (Code α)

forUnfold : ∀ ⦃ _ : C ⦄ → ∀ { α } → Producer α → Producer α
forUnfold { α } (producer { σ = σ } (init , for (bound , index))) =
  let init' : ∀ { ω } → ((Ref Int × σ) → Code ω) → Code ω
      init' k = init (λ s0 → decl Int λ i → i ≔ ⟨ int 0 ⟩ ； k (i , s0))
      term : (Ref Int × σ) → Code Bool
      term pair = (let i , s0 = pair in (★ i) <= bound s0)
      step : (Ref Int × σ) →  (α → Code Void) → Code Void
      step pair k =
        let i , s0 = pair in
          index s0 (★ i) (λ a → i ≔ (★ i) + ⟨ int 1 ⟩ ； k a)
  in
    producer (init' , unfolder (term , many , step))
forUnfold (producer (init , unfolder x)) =
  producer (init , unfolder x)

ofArr : ∀ ⦃ _ : C ⦄ → ∀ { α n } → Code (Array α n) → Stream α
ofArr { α } { n } arr =
  let init : ∀ { ω } → (Ref (Array α n) → Code ω) → Code ω
      init k = decl (Array α n) λ x → x ≔ arr ； k x
      upb : ∀ { m } → Ref (Array α m) → Code Int
      upb { m } _ = ⟨ int m ⟩
      index : ∀ { m } → Ref (Array α m) → Code Int → (Code α → Code Void) → Code Void
      index arr i k = decl α λ el → el ≔ ★ (arr [ i ]) ； k (★ el) -- TODO: requires i ∈ n
  in
    linear (producer (init , for (upb , index)))

-- TODO: C optionals / limited C structs
unfold : ∀ ⦃ _ : C ⦄ → ∀ { α ζ }
  → (Code ζ → Code Bool × Code α × Code ζ) → Code ζ → Stream α
unfold { α } { ζ } f x =
  let init : ∀ { ω } → (Code Bool × Code α × Code ζ → Code ω) → Code ω
      init k = k (f x)
      term : Code Bool × Code α × Code ζ → Code Bool
      term tuple = (let b , _ = tuple in b)
      step : Code Bool × Code α × Code ζ → (Code α → Code Void) → Code Void
      step s body = 
        let b , a , z = s in
        let b' , a' , z' = f z in
          if b then
            body a'
          else nop
  in
    linear (
      producer ((init , unfolder (term , many , step)))
    )

{-# TERMINATING #-} -- TODO: coinduction
foldRaw : ∀ ⦃ _ : C ⦄ → ∀ { α } → (α → Code Void) → SStream α → Code Void
foldRaw consumer (linear (producer (init , for (bound , index)))) = 
  init (λ sp → for ⟨ int 0 ⟩ to bound sp then λ i → index sp (★ i) consumer)
foldRaw consumer (linear (producer (init , unfolder (term , atMost1 , step)))) =
  init λ sp → if term sp then step sp consumer ； nop  else nop
foldRaw consumer (linear (producer (init , unfolder (term , many , step)))) =
  init λ sp → while term sp then step sp consumer
foldRaw consumer (nested (prod , f)) =
  foldRaw (λ e → foldRaw consumer (f e)) (linear prod)

fold : ∀ ⦃ _ : C ⦄ → ∀ { α ζ } → (Code ζ → Code α → Code ζ) → Code ζ → Stream α → Code ζ
fold { ζ = ζ } f z s =
  decl ζ λ acc →
  acc ≔ z ；
  foldRaw (λ a → acc ≔ f (★ acc) a) s ；
  ★ acc

mapRaw : ∀ ⦃ _ : C ⦄ → ∀ { α β } → (α → (β → Code Void) → Code Void)
  → SStream α → SStream β
mapRaw tr (linear (producer (init , for (bound , index)))) =
  let index' s i k = index s i (λ e → tr e k) in
    linear (producer (init , for (bound , index')))
mapRaw tr (linear (producer (init , unfolder (term , card , step)))) =
  let step' s k = step s (λ e → tr e k) in
    linear (producer (init , unfolder (term , card , step')))
mapRaw tr (nested (p , f)) = nested (p , (λ a → mapRaw tr (f a)))

map : ∀ ⦃ _ : C ⦄ → ∀ { α β } → (Code α → Code β) → Stream α → Stream β
map { β = β } f =
  mapRaw (λ a k →
    decl β λ t →
    t ≔ f a ；
    k (★ t)
  )

flatMap : ∀ ⦃ _ : C ⦄ → ∀ { α β } → (α → SStream β) → SStream α → SStream β
flatMap {α = α} f (linear x) = nested (x , f)
flatMap f (nested (x , g)) = nested (x , λ a → flatMap f (g a))

filter : ∀ ⦃ _ : C ⦄ → ∀ { α : c_type } → (Code α → Code Bool) → Stream α → Stream α
filter { α = α } f = flatMap (
  λ x → linear (
    producer (
      (λ k → k x)
      , unfolder (f , atMost1 , λ a k → k a)
    )
  ))

{-# TERMINATING #-} -- TODO
addToProducer : ∀ ⦃ _ : C ⦄ → ∀ { α } → Code Bool → Producer α → Producer α
addToProducer new (producer (init , unfolder (term , many , step))) =
  producer ((init , unfolder ((λ s → new && term s) , many , step)))
addToProducer new (producer (init , unfolder (term , atMost1 , step))) =
  producer (init , unfolder (term , atMost1 , step))
addToProducer new (producer (init , for x)) =
  addToProducer new (forUnfold (producer (init , for x)))

moreTermination : ∀ ⦃ _ : C ⦄ → ∀ { α } → Code Bool → SStream α → SStream α
moreTermination new (linear p) = linear (addToProducer new p)
moreTermination new (nested (p , f)) =
  nested (addToProducer new p , λ a → moreTermination new (f a))

addNr : ∀ ⦃ _ : C ⦄ → ∀ { α } → Code Int → (p : Producer α) → Producer (Ref Int × α)
addNr n (producer { σ = σ } (init , unfolder (term , card , step))) =
  let init' : ∀ { ω } → (Ref Int × σ → Code ω) → Code ω
      init' k = init (λ s → decl Int λ nr → k (nr , s))
      term' : CardT → Ref Int × σ → Code Bool
      term' = λ { many (nr , s) → (★ nr) == ⟨ int 0 ⟩ && term s
                ; atMost1 (nr , s) → term s }
      step' nrs k =
        let nr , s = nrs in
          step s (λ el → k (nr , el))
  in
    producer (init' , unfolder (term' card , card , step'))
addNr _ (producer (_ , for _)) =
  producer ((λ k → k ⊤.tt) , for ((λ _ → ⟨ int 0 ⟩) , (λ _ _ _ → nop)))

take : ∀ ⦃ _ : C ⦄ → Code Int → ∀ { α } → SStream α → SStream α
take n (linear (producer (init , for (bound , index)))) =
  linear (producer (
    init , for ((λ s → if (n - ⟨ int 1 ⟩) < bound s then n - ⟨ int 1 ⟩ else bound s) , index))
  )
take n (linear (producer (init , unfolder x))) =
  mapRaw
    (λ nrel k → let nr , el = nrel in nr ≔ ★ nr - ⟨ int 1 ⟩ ； k el)
    (linear (addNr n (producer (init , unfolder x))))
take n (nested { β = α } (p , f)) =
  nested (
    addNr n (forUnfold p) ,
    λ nra →
      let nr , a = nra in
        mapRaw
          (λ el k → nr ≔ ★ nr - ⟨ int 1 ⟩ ； k el)
          (moreTermination ((★ nr) == ⟨ int 0 ⟩) (f a))
  )

iota : ∀ ⦃ _ : C ⦄ → ℕ → Stream Int
iota n = unfold (λ n → true , n , n + ⟨ int 1 ⟩) ⟨ int n ⟩

--------------------------------------------------------------------------

module Eval where

  applyOperator : ∀ { α β γ Γ : Set } → (α → β → γ) → State Γ α → State Γ β → State Γ γ
  applyOperator f x y state =
    let x' , state' = x state in
    let y' , state'' = y state' in
      f x' y' , state''

  encode : ∀ { α : c_type } → ⟦ α ⟧ → ℤ
  encode { Void } _ = int 0
  encode { Char } = int ∘ Data.Char.toℕ
  encode { Int } = id
  encode { Bool } Data.Bool.false = int 0
  encode { Bool } Data.Bool.true = int 1
  encode { Array α n } x = int 0 -- Do not use, should be able to force this by typing...

  updateMapForArray :
    ∀ { α n } → String → ⟦ Array α n ⟧ → (String → ℤ) → (String → ℤ)
  updateMapForArray name []ᵥ = id
  updateMapForArray {_} {ℕ.suc n} name (x ∷ᵥ arr) f =
    let f' = updateMapForArray name arr f in
      λ var →
        If var ==ₛ name ++ (Data.Nat.Show.show n)
        then encode x else f' name

  safediv : ℤ → ℤ → ℤ
  safediv x (int 0) = int 0
  safediv x Data.Integer.+[1+ n ] = x /ᵢ (Data.Integer.+[1+ n ])
  safediv x (ℤ.negsuc n) = x /ᵢ (ℤ.negsuc n)

  impl : C
  C.Code impl α = State (String → ℤ) ⟦ α ⟧
  C.Ref impl α = C.Code impl α
  --(impl C.∈ x) n = let x' , _ = x (λ _ → int 0) in (int 0 <ᵢ x') × (x' <ᵢ int n)
  C.⟨ impl ⟩ n state = n , state
  (impl C.+ x) y = applyOperator (_+ᵢ_) x y
  (impl C.* x) y = applyOperator (_*ᵢ_) x y
  (impl C.- x) y = applyOperator (_-ᵢ_) x y
  (impl C./ x) y state = 
    let x' , state' = x state in
    let y' , state'' = y state' in
      (safediv x' y') , state''
  C.true impl state = Data.Bool.true , state
  C.false impl state = Data.Bool.false , state
  (impl C.|| x) y = applyOperator Data.Bool._∨_ x y
  (impl C.&& x) y = applyOperator Data.Bool._∧_ x y
  (C.if impl then cond else a) b state =
    let cond' , state' = cond state in
      (If cond' then a else b) state'
  C.[] impl state = []ᵥ , state
  (impl C.∷ x) y = applyOperator (_∷ᵥ_) x y
  C._[_] impl {_} {n} arr i state = {!!}
  (C.★ impl) x state = {!!}
  C._≔_ impl x y state = {!!}
  (impl C.； x) f state = {!!}
  C.decl impl α f state = {!!}

eval : ∀ { α : c_type } → (∀ ⦃ impl : C ⦄ → Code ⦃ impl ⦄ α) → ⟦ α ⟧
eval e = let v , _ = e ⦃ Eval.impl ⦄ (λ _ → int 0) in v

open import IO
main =
  let ex = eval (⟨ int 1 ⟩) in
    run (IO.putStr (Data.Integer.show ex))
