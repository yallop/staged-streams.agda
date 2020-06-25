open import C.Base
open import C.Extras
open import Data.Integer as ℤ using (+_)
open import Data.List as List using (List ; _∷_ ; [])
open import Data.Maybe as Maybe using (Maybe ; just ; nothing)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product as Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String as String using (String ; _++_)
open import Data.Vec as Vec using (Vec ; _∷_ ; [])
open import IO
open import Print.Print
open import Streams

import Data.Nat.Show as ℕs
import Data.Fin as Fin
import Data.Nat.DivMod as ℕ÷

module Benchmark where

record CWithExtras : Set₁ where
  field
    ⦃ ℐ ⦄ : C
    declBigInt : (C.Ref ℐ Int → C.Statement ℐ) → C.Statement ℐ
    printInt : C.Expr ℐ Int → C.Statement ℐ
    printBigInt : C.Expr ℐ Int → C.Statement ℐ

open C ⦃ ... ⦄
open CWithExtras ⦃ ... ⦄

-- Kiselyov et al., Section §7:
--
-- - sum: the simplest of_arr arr ▹ sum pipeline, summing the elements of an array;
-- - sumOfSquares: our running example from §4.2 on;
-- - sumOfSquaresEven: the sumOfSquares benchmark with added filter, summing the squares of only the even array elements;
-- - cart: ∑ xᵢ yⱼ, using flat_map to build the outer-product stream;
-- - maps: consecutive map operations with integer multiplication;
-- - filters: consecutive filter operations using integer comparison;
-- - dotProduct: compute dot product of two arrays using zip_with;
-- - flatMapafterzipWith: compute ∑ (xᵢ+xᵢ) yⱼ, like cart above, doubling the x array via zip_with (+) with itself;
-- - zipWithafterflatMap: zip_with of two streams one of whichis the result of flat_map;
-- - flatmaptake: flat_map followed by take"
--
-- Input: All tests were run with the same input set. For the sum, sumOfSquares, sumOfSquaresEven, maps, filters we used an array of N = 100,000,000 small integers: xᵢ = i mod 10. The cart test iterates over two arrays. An outer one of 10,000,000 integers and an inner one of 10. For the dotProduct we used 10,000,000 integers, for the flatMap_after_zipWith 10,000, for the zipWith_after_flatMap 10,000,000 and for the flatmap_take N numbers sub-sized by 20% of N."

module Tests ⦃ _ : CWithExtras ⦄ where
  sum : Ref (Array Int 1000000000) → Ref Int → Statement
  sum arr len =
    declBigInt λ r →
    r ← fold _+_ ⟪ + 0 ⟫ (take (★ len) (ofArr arr)) ；
    printBigInt (★ r)

  sumOfSquares : Ref (Array Int 1000000000) → Ref Int → Statement
  sumOfSquares arr len =
    declBigInt λ r →
    r ← fold _+_ ⟪ + 0 ⟫
      ((take (★ len) (ofArr arr)) ▹ map (λ a → a * a)) ；
    printBigInt (★ r)

  sumOfSquaresEven : Ref (Array Int 1000000000) → Ref Int → Statement
  sumOfSquaresEven arr len =
    declBigInt λ r →
    r ← fold _+_ ⟪ + 0 ⟫
      ((take (★ len) (ofArr arr))
        ▹ filter (λ e → (e % ⟪ + 2 ⟫) == ⟪ + 0 ⟫)
        ▹ map (λ a → a * a)) ；
    printBigInt (★ r)

  -- Sum over Cartesian-/outer-product
  cart : Ref (Array Int 1000000000) → Ref Int → Ref (Array Int 1000000000) → Ref Int → Statement
  cart arr₁ len₁ arr₂ len₂ =
    declBigInt λ r →
    r ← fold _+_ ⟪ + 0 ⟫
      ((take (★ len₁) (ofArr arr₁)) ▹ flatmap (λ i → (take (★ len₂) (ofArr arr₂)) ▹ map (λ j → i * j))) ；
    printBigInt (★ r)

  maps : Ref (Array Int 1000000000) → Ref Int → Statement
  maps arr len =
    iter (λ e → printInt e)
      ((take (★ len) (ofArr arr))
        ▹ map (λ e → e * ⟪ + 2 ⟫)
        ▹ map (λ e → e * ⟪ + 3 ⟫))

  filters : Ref (Array Int 1000000000) → Ref Int → Statement
  filters arr len =
    iter (λ e → printInt e)
      ((take (★ len) (ofArr arr))
        ▹ filter (λ e → ! ((e % ⟪ + 5 ⟫) == ⟪ + 0 ⟫))
        ▹ filter (λ e → ! ((e % ⟪ + 8 ⟫) == ⟪ + 0 ⟫)))

  dotProduct : Ref (Array Int 1000000000) → Ref Int → Ref (Array Int 1000000000) → Ref Int → Statement
  dotProduct arr₁ len₁ arr₂ len₂ =
    declBigInt λ r →
    r ← fold _+_ ⟪ + 0 ⟫
      (zipWith (λ i j → i * j) (take (★ len₁) (ofArr arr₁)) (take (★ len₂) (ofArr arr₂)) {ℕ.z≤n}) ；
    printBigInt (★ r)

  flatmap-after-zipWith : Ref (Array Int 1000000000) → Ref Int → Ref (Array Int 1000000000) → Ref Int → Statement
  flatmap-after-zipWith arr₁ len₁ arr₂ len₂ =
    iter (λ e → printInt e)
      (zipWith _+_ (take (★ len₁) (ofArr arr₁)) (take (★ len₁) (ofArr arr₁)) {ℕ.z≤n}
        ▹ flatmap (λ i → (take (★ len₂) (ofArr arr₂)) ▹ map (λ j → i * j)))

  zipWith-after-flatmap : Ref (Array Int 1000000000) → Ref Int → Ref (Array Int 1000000000) → Ref Int → Statement
  zipWith-after-flatmap arr₁ len₁ arr₂ len₂ =
    iter (λ e → printInt e)
      (zipWith _+_ (take (★ len₁) (ofArr arr₁)) (flatmap (λ e → (take (★ len₂) (ofArr arr₂)) ▹ map (λ a → a + e)) (take (★ len₁) (ofArr arr₁))) {ℕ.s≤s ℕ.z≤n})

  flatmap-take : Ref (Array Int 1000000000) → Ref Int → Ref (Array Int 1000000000) → Ref Int → Statement
  flatmap-take arr₁ len₁ arr₂ len₂ =
    iter (λ e → printInt e)
      ((take (★ len₁) (ofArr arr₁))
        ▹ flatmap (λ a → (take (★ len₂) (ofArr arr₂)) ▹ map (λ b → a + b))
        ▹ take ⟪ + 20000000 ⟫)

print-c-decl : (α : c_type) → (String → (ℕ → ℕ × String)) → (ℕ → ℕ × String)
print-c-decl α f n =
  let ref = "x" ++ ℕs.show n in
  let n , f = f ref (ℕ.suc n) in
    n , builder α ref ++ ";\n" ++ f
  where
    builder : c_type → String → String
    builder Int acc = "int64_t " ++ acc
    builder Bool acc = "/* BOOL */ int " ++ acc
    builder (Array α n) acc = builder α (acc ++ "[" ++ ℕs.show n ++ "]")

AST-CWithExtras : CWithExtras
CWithExtras.ℐ AST-CWithExtras = record Print-C {
    -- the first few fields are here because Agda complains about
    -- unsolved metas for the implicit arguments if they're copied
    -- over implicitly
    _[_] = λ {c n} → C._[_] Print-C {c} {n};
    ★_ = λ {α} → C.★_ Print-C {α};
    _⁇_∷_ = λ {α} → C._⁇_∷_ Print-C {α};
    _≔_ = λ {α} → C._≔_ Print-C {α};
    decl = print-c-decl
 }
CWithExtras.declBigInt AST-CWithExtras f n =
  let ref = "x" ++ ℕs.show n in
  let n , f = f ref (ℕ.suc n) in
    n , "int64_t " ++ ref ++ ";\n" ++ f
CWithExtras.printInt AST-CWithExtras e n = n , "printf(\"%d\\n\", " ++ e ++ ");\n"
CWithExtras.printBigInt AST-CWithExtras e n = n , "printf(\"%lld\\n\", " ++ e ++ ");\n"

benchmark-function : String → (∀ ⦃ _ : CWithExtras ⦄ → Ref (Array Int 1000000000) → Ref Int → Statement) → String
benchmark-function name body =
  "int64_t " ++ name ++ "(int64_t *arr, int64_t len)\n"
    ++ "{\n"
    ++ proj₂ (body ⦃ AST-CWithExtras ⦄ "arr" "len" 0)
    ++ "return x0;\n"
  ++ "}\n"

benchmark-function2 : String → (∀ ⦃ _ : CWithExtras ⦄ → Ref (Array Int 1000000000) → Ref Int → Ref (Array Int 1000000000) → Ref Int → Statement) → String
benchmark-function2 name body =
  "int64_t " ++ name ++ "(int64_t *arr1, int64_t len1, int64_t *arr2, int64_t len2)\n"
    ++ "{\n"
    ++ proj₂ (body ⦃ AST-CWithExtras ⦄ "arr1" "len1" "arr2" "len2" 0)
    ++ "return x0;\n"
  ++ "}\n"

main =
  run (IO.putStr ex)
  where
    ex : String
    ex =
      "#include <stdio.h>\n"
      ++ "#include <stdlib.h>\n"
      ++ "#include <stdint.h>\n"
      ++ (benchmark-function "sum" Tests.sum)
      ++ (benchmark-function "sumOfSquares" Tests.sumOfSquares)
      ++ (benchmark-function "sumOfSquaresEven" Tests.sumOfSquaresEven)
      ++ (benchmark-function2 "cart" Tests.cart)
      ++ (benchmark-function "maps" Tests.maps)
      ++ (benchmark-function "filters" Tests.filters)
      ++ (benchmark-function2 "dotProduct" Tests.dotProduct)
      ++ (benchmark-function2 "flatmap_after_zipWith" Tests.flatmap-after-zipWith)
      ++ (benchmark-function2 "zipWith_after_flatmap" Tests.zipWith-after-flatmap)
      ++ (benchmark-function2 "flatmap_take" Tests.flatmap-take)
