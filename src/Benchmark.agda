open import C.Base
open import C.Extras
open import Data.Integer as ℤ using (+_)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product as Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String as String using (String ; _++_)
open import IO
open import Print.Print
open import Streams

import Data.Nat.Show as ℕs

module Benchmark where

open C ⦃ ... ⦄
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
-- Input: All tests were run with the same input set. For the sum,
-- sumOfSquares, sumOfSquaresEven, maps, filters we used an array of N
-- 100,000,000 small integers: xᵢ = i mod 10. The cart test iterates
-- over two arrays. An outer one of 10,000,000 integers and an inner
-- one of 10. For the dotProduct we used 10,000,000 integers, for the
-- flatMap_after_zipWith 10,000, for the zipWith_after_flatMap
-- 10,000,000 and for the flatmap_take N numbers sub-sized by 20% of
-- N."


module Tests ⦃ _ : C ⦄ where
  one-hole-context = Ref Int → Statement
  one-arr-test = Ref (Array Int 1000000000) → Ref Int → one-hole-context
  two-arr-test = Ref (Array Int 1000000000) → Ref Int → one-arr-test
  of-arr[_] : Ref Int → Ref (Array Int 1000000000) → Stream Int
  of-arr[_] len arr = take (★ len) (ofArr arr)

  sum : one-arr-test
  sum arr len =
    of-arr[ len ] arr
    ▹ fold _+_ ⟪ + 0 ⟫ 

  sumOfSquares : one-arr-test
  sumOfSquares arr len =
    of-arr[ len ] arr
    ▹ map (λ x → x * x)
    ▹ fold _+_ ⟪ + 0 ⟫ 

  sumOfSquaresEven : one-arr-test
  sumOfSquaresEven arr len =
    of-arr[ len ] arr
    ▹ filter (λ x → (x % ⟪ + 2 ⟫) == ⟪ + 0 ⟫)
    ▹ map (λ x → x * x)
    ▹ fold _+_ ⟪ + 0 ⟫

  cart : two-arr-test
  cart arr₁ len₁ arr₂ len₂ =
         of-arr[ len₁ ] arr₁
       ▹ flatmap (λ x → of-arr[ len₂ ] arr₂
                         ▹ map (λ y → x * y))
       ▹ fold _+_ ⟪ + 0 ⟫

  maps : one-arr-test
  maps arr len =
     of-arr[ len ] arr
      ▹ map (λ x → x * ⟪ + 1 ⟫)
      ▹ map (λ x → x * ⟪ + 2 ⟫)
      ▹ map (λ x → x * ⟪ + 3 ⟫)
      ▹ map (λ x → x * ⟪ + 4 ⟫)
      ▹ map (λ x → x * ⟪ + 5 ⟫)
      ▹ map (λ x → x * ⟪ + 6 ⟫)
      ▹ map (λ x → x * ⟪ + 7 ⟫)
      ▹ fold _+_ ⟪ + 0 ⟫

  filters : one-arr-test
  filters arr len =
      of-arr[ len ] arr
        ▹ filter (λ x → x > ⟪ + 1 ⟫)
        ▹ filter (λ x → x > ⟪ + 2 ⟫)
        ▹ filter (λ x → x > ⟪ + 3 ⟫)
        ▹ filter (λ x → x > ⟪ + 4 ⟫)
        ▹ filter (λ x → x > ⟪ + 5 ⟫)
        ▹ filter (λ x → x > ⟪ + 6 ⟫)
        ▹ filter (λ x → x > ⟪ + 7 ⟫)
        ▹ fold _+_ ⟪ + 0 ⟫

  dotProduct : two-arr-test
  dotProduct arr₁ len₁ arr₂ len₂ =
      zipWith _*_ (of-arr[ len₁ ] arr₁) (of-arr[ len₂ ] arr₂) {ℕ.z≤n}
      ▹ fold _+_ ⟪ + 0 ⟫

  flatmap-after-zipWith : two-arr-test
  flatmap-after-zipWith arr₁ len₁ arr₂ len₂ =
    zipWith _+_ (of-arr[ len₁ ] arr₁) (of-arr[ len₁ ] arr₁) {ℕ.z≤n}
        ▹ flatmap (λ x → of-arr[ len₂ ] arr₂ ▹ map (λ el → el * x))
        ▹ fold _+_ ⟪ + 0 ⟫

  zipWith-after-flatmap : two-arr-test
  zipWith-after-flatmap arr₁ len₁ arr₂ len₂ =
     (zipWith _+_ (of-arr[ len₁ ] arr₁) (flatmap (λ e → of-arr[ len₂ ] arr₂ ▹ map (λ a → a + e)) (of-arr[ len₁ ] arr₁)) {ℕ.s≤s ℕ.z≤n})
      ▹ fold _+_ ⟪ + 0 ⟫

  flatmap-take : two-arr-test
  flatmap-take arr₁ len₁ arr₂ len₂ =
      of-arr[ len₁ ] arr₁
      ▹ flatmap (λ x → of-arr[ len₂ ] arr₂ ▹ map (λ y → x + y))
      ▹ take ⟪ + 20000000 ⟫
      ▹ fold _+_ ⟪ + 0 ⟫

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

-- like Print-C but use int64_t for integers
Print-C' : C
Print-C' = record Print-C {
    -- we just want to override 'decl'; the other fields are here
    -- because Agda complains about unsolved metas for the implicit
    -- arguments if they're copied over implicitly
    _[_] = λ {c n} → C._[_] Print-C {c} {n};
    ★_ = λ {α} → C.★_ Print-C {α};
    _⁇_∷_ = λ {α} → C._⁇_∷_ Print-C {α};
    _≔_ = λ {α} → C._≔_ Print-C {α};
    decl = print-c-decl
 }

benchmark-function : String → (⦃ _ : C ⦄ → Tests.one-arr-test) → String
benchmark-function name body =
  "int64_t " ++ name ++ "(int64_t *arr, int64_t len)\n"
    ++ "{\n"
    ++ "int64_t rv;\n"
    ++ proj₂ (body ⦃ Print-C' ⦄ "arr" "len" "rv" 0)
    ++ "return rv;\n"
  ++ "}\n"

benchmark-function-2 : String → (⦃ _ : C ⦄ → Tests.two-arr-test) → String
benchmark-function-2 name body =
  "int64_t " ++ name ++ "(int64_t *arr1, int64_t len1, int64_t *arr2, int64_t len2)\n"
    ++ "{\n"
    ++ "int64_t rv;\n"
    ++ proj₂ (body ⦃ Print-C' ⦄ "arr1" "len1" "arr2" "len2" "rv" 0)
    ++ "return rv;\n"
  ++ "}\n"

main =
  run (IO.putStr ex)
  where
    ex : String
    ex = "#include <stdint.h>\n"
      ++ (benchmark-function   "sum" Tests.sum)
      ++ (benchmark-function   "sumOfSquares" Tests.sumOfSquares)
      ++ (benchmark-function   "sumOfSquaresEven" Tests.sumOfSquaresEven)
      ++ (benchmark-function-2 "cart" Tests.cart)
      ++ (benchmark-function   "maps" Tests.maps)
      ++ (benchmark-function   "filters" Tests.filters)
      ++ (benchmark-function-2 "dotProduct" Tests.dotProduct)
      ++ (benchmark-function-2 "flatmap_after_zipWith" Tests.flatmap-after-zipWith)
      ++ (benchmark-function-2 "zipWith_after_flatmap" Tests.zipWith-after-flatmap)
      ++ (benchmark-function-2 "flatmap_take" Tests.flatmap-take)
