{-# OPTIONS_GHC #-}

-- Module      :  Data.Complex.CZ
-- Copyright   :  (c) Scott N. Walck 2012
-- License     :  GPL-3 (see LICENSE)
-- Maintainer  :  Scott N. Walck <walck@lvc.edu>

{- | The cyclotomic numbers are a subset of the complex numbers with
     the following properties:
    
     1.  The cyclotomic numbers are represented exactly, enabling exact
     computations and equality comparisons.
    
     2.  The cyclotomic numbers contain the Gaussian rationals
     (complex numbers of the form 'p' + 'q' 'i' with 'p' and 'q' rational).
     As a consequence, the cyclotomic numbers are a dense subset of the
     complex numbers.
    
     3.  The cyclotomic numbers contain the square roots of all rational numbers.
    
     4.  The cyclotomic numbers form a field:  they are closed under addition, subtraction,
     multiplication, and division.
    
     5.  The cyclotomic numbers contain the sine and cosine of all rational
     multiples of pi.
    
     6.  The cyclotomic numbers can be thought of as the rational field extended
     with 'n'th roots of unity for arbitrarily large integers 'n'.

     Floating point numbers do not do well with equality comparison:

>(sqrt 2 + sqrt 3)^2 == 5 + 2 * sqrt 6
> -> False

     "Data.Complex.CZ" represents these numbers exactly, allowing equality comparison:

>(sqrtRat 2 + sqrtRat 3)^2 == 5 + 2 * sqrtRat 6
> -> True

     'CZ's can be exported as inexact complex numbers using the 'toComplex2' function:

>e 6
> -> -e(3)^2
>real $ e 6
> -> 1/2
>imag $ e 6
> -> -1/2*e(12)^7 + 1/2*e(12)^11
>imag (e 6) == sqrtRat 3 / 2
> -> True
>toComplex2 $ e 6
> -> 0.5000000000000003 :+ 0.8660254037844384

     The algorithms for cyclotomic numbers are adapted from code by
     Martin Schoenert and Thomas Breuer in the GAP project <http://www.gap-system.org/>
     (in particular source files gap4r4\/src\/cyclotom.c and
     gap4r4\/lib\/cyclotom.gi).
-}

module Data.Complex.Cyclotomic
    (CZ
    ,i
    ,e
    ,sqrtInteger
    ,sqrtRat
    ,sinDeg
    ,cosDeg
    ,gaussianRat
    ,polarRat
    ,conj
    ,real
    ,imag
    ,modSq
    ,isReal
    ,isRat
    ,isGaussianRat
    ,toComplex2
    ,toReal
    ,toRat
    -- added by dd
    ,fromQ
    ,fromZ
    ,toZr1
    ,toZrN
    -- higher square roots
    ,sqrt3
    ,sqrt5
    ,invert
    ,bsearch
    ,birdFactor
    ,findBS
    ,apd3
    ,rr2
    ,sqrt6
    ,ee
    )
    where

import Data.List (nub)
import Data.Ratio
import Data.Complex
import qualified Data.Map as M
import Math.NumberTheory.Primes.Factorisation (factorise)


import Math.NumberTheory.GCD (binaryGCD, extendedGCD, coprime)
import Math.NumberTheory.Logarithms
import Math.NumberTheory.Moduli
import Math.NumberTheory.MoebiusInversion
import Math.NumberTheory.Powers
import Math.NumberTheory.Lucas (fibonacci,lucas,fibonacciPair,lucasPair,generalLucas)


-- | A cyclotomic number.
data CZ = CZ { order  :: Integer                  --      used 3x    in toComplex2, tryRat, tryReduce
             , coeffs :: M.Map Integer Rational   -- only used once, in toComplex2
             } deriving (Eq, Ord)

fromQ :: Rational -> CZ
fromZ :: Integral a => a -> CZ
toZr1 :: CZ
toZrN :: Integer -> CZ

fromQ r = CZ 1                   (M.singleton 0 r               )
fromZ n = CZ 1                   (M.singleton 0 (fromIntegral n))
toZr1   = CZ 1                   (M.singleton 0 1               )
toZrN n = cyclotomic n $ convertToBase n (M.singleton 1 1               )

-- | @signum c@ is the complex number with magnitude 1 that has the same argument as c;
--   @signum c = c / abs c@.
instance Num CZ where
    (+)                  =  sumCyc
    (*)                  = prodCyc
    (-) c1 c2            =  sumCyc c1 (aInv_1_CZ c2)
    negate               = aInv_1_CZ
    abs                  = sqrtRat . modSq
    signum      0        = zeroCyc
    signum        c      = c / abs c
    fromInteger 0        = zeroCyc
    fromInteger     n    = negate $ CZ 1 (M.singleton 0 (fromIntegral n))


testt n = map (\n ->  CZ 0 (M.singleton 0 (fromIntegral n))) [0,0,0,1,1,2,2,3,4,8,9,9]

{-
instance Real CZ where
     toRational = undefined

instance Enum CZ where
     succ n           = n + 1
     pred n           = n - 1
     toEnum   0       = zeroCyc
     toEnum   n       = CZ 1 (M.singleton 0 (fromIntegral n))
     fromEnum zeroCyc = 0
     fromEnum cyc     = undefined


instance Integral CZ where
     quotRem a b = let (d,m) = divMod a b in
                         if (signum d < zeroCyc) then
                              (d + 1, m - b) else (d, m )
     toInteger zeroCyc = 0
     toInteger  n      = 2
-}

instance Fractional CZ where
    recip          = mInv_2_CZ
    fromRational 0 = zeroCyc
    fromRational r = CZ 1 (M.singleton 0 r)

-- | The primitive @n@th root of unity.
--   For example, @'e'(4) = 'i'@ is the primitive 4th root of unity,
--   and 'e'(5) = exp(2*pi*i/5) is the primitive 5th root of unity.
--   In general, 'e' 'n' = exp(2*pi*i/'n').
e :: Integer -> CZ
e n
    | n < 1      = error "e requires a positive integer"
    | n == 1     = CZ 1 (M.singleton 0 1)                                  --  1 :===: 0 :-->: 1
    | otherwise  = cyclotomic n $ convertToBase n (M.singleton 1 1)

ee :: Integer -> CZ
ee n
    | n < 1      = error "e requires a positive integer"
    | n == 1     = CZ 4                           (M.singleton 0 2)
    | otherwise  = cyclotomic n $ convertToBase n (M.singleton 2 4)


{-
showBaseExp :: Integer -> Integer -> String
showBaseExp n 1  = " e( " ++ show n ++ " )  "
showBaseExp n ex = " e( " ++ show n ++ " )^ " ++ show ex
-}

showBaseExp :: Integer -> Integer -> String
showBaseExp n 1  =              " (e " ++ show n ++ ")  "
showBaseExp n ex =              " (e " ++ show n ++ ")^ " ++ show ex

instance Show CZ where
    show c@(CZ n mp)
        | mp == M.empty  = "000"
        | otherwise      = leadingTerm c rat n ex ++ followingTerms c n xs
        where ((ex,rat):xs) = M.toList mp

-- this careful spacing still fails because
-- the dynamic part of the layout (showRat r) doesn't report the text width.
leadingTerm :: CZ -> Rational -> Integer -> Integer -> String
leadingTerm _ r _ 0 = showRat r
leadingTerm _ r n ex
    | r ==   1   = "\t   \t"                    ++ "\t   \t" ++ t ++ "\n"
    | r == (-1)  = "\t - \t"                    ++ "\t   \t" ++ t ++ "\n"
    | r > 0      = "\t + \t" ++ showRat      r  ++ "\t * \t" ++ t ++ "\n"
    | r < 0      = "\t - \t" ++ showRat (abs r) ++ "\t * \t" ++ t ++ "\n"
    | otherwise  =                               "#####"
    where t = showBaseExp n ex

followingTerms :: CZ -> Integer -> [(Integer,Rational)] -> String
followingTerms c _ [        ]    =
                              "\n" ++ "\t is      real?    : \t" ++ show (isReal            c )     ++ 
                              "\n" ++ "\t is       rat?    : \t" ++ show (isRat             c )     ++ 
                              "\n" ++ "\t is Gauss rat?    : \t" ++ show (isGaussianRat     c )     ++ 
                              "\n" ++ "\t rational      form: \t\t" ++ show (toRat           c )     ++ 
                              "\n" ++ "\t i = sqrt(-01) form: \t\t" ++ show (toComplex2       c )     ++
                              "\n" ++ "\t i = sqrt(-03) form: \t\t" ++ show (toComplex3       c )     ++
                              "\n" ++ "\t i = sqrt(-23) form: \t\t" ++ show (toComplex23      c )     ++
                              "\n" ++ "\t conjugate    form: \t\t" ++ show (toComplex2 (conj   c))     ++ 
                              "\n" ++ "\t (+) <-> (-)  form: \t\t" ++ show (toComplex2 (aInv_1_CZ (negate c)))    ++    -- could fail, so it must go last?
                              "\n" ++ "\t (*) <-> (/)  form: \t\t" ++ show (toComplex2 (mInv_2_CZ c))              



followingTerms c n ((ex,rat):xs) = followingTerm c rat n ex ++ followingTerms c n xs

followingTerm :: CZ -> Rational -> Integer -> Integer -> String
followingTerm c r n ex
    | r ==   1   = "\t + \t"                    ++  "\t   \t" ++ t ++ "\n"
    | r == (-1)  = "\t - \t"                    ++  "\t   \t" ++ t ++ "\n"
    | r > 0      = "\t + \t" ++ showRat      r  ++  "\t * \t" ++ t ++ "\n" 
    | r < 0      = "\t - \t" ++ showRat (abs r) ++  "\t * \t" ++ t ++ "\n"
    | otherwise  = "\t   \t"
    where t = showBaseExp n ex

showRat :: Rational -> String
showRat r
    | d == 1     = show n
    | otherwise  = show n ++ "/" ++ show d
    where
      n = numerator r
      d = denominator r

-- GAP function EB from gap4r4/lib/cyclotom.gi
eb :: Integer -> CZ
eb n
    | n < 1           = error "eb needs a positive integer"
    | n `mod` 2 /= 1  = error "eb needs an odd integer"
    | n == 1          = zeroCyc
    | otherwise       = let en = e n
                        in sum [en^(k*k `mod` n) | k <- [1..(n-1) `div` 2]]

sqrt2 :: CZ
sqrt3 :: CZ
sqrt5 :: CZ

sqrt2 = e  8               -  e 8  ^ ( 3 :: Int)
sqrt3 = e 12 ^ (11 :: Int) -  e 12 ^ ( 7 :: Int)
sqrt5 = (e 5) - (e 5)^(2 :: Int) - (e 5)^(3 :: Int) + (e 5)^(4 :: Int)
sqrt6 = sqrt 2 * sqrt 3

-- rr = "real root"
-- ir = "imaginary root"

rr2 = sqrt2 -- silver ratio - 1  (aka, we're setting 1 equal to the silver ratio)

-- ^
-- >>> toReal $ sqrt2
-- Just 1.414213562373095

-- ^
-- >>> toComplex2 $ sqrt2
-- 1.414213562373095 :+ (-2.220446049250313e-16)
-- it :: Complex Double
-- (0.00 secs, 522012 bytes)


-- we can view this strange thing in two ways (if either is correct):
--
--  

light   = negate (1 /(-12)) + (1/(-12)) * ir23
medium  = negate (13/(-24)) + (1/24) * ir23
heavy   = negate (25/(-36)) + (1/36) * ir23



ir23 = sqrtInteger (-23)

golden :: CZ
golden = (1 + sqrtInteger 5) / 2

prPhi  = (1 + sqrtInteger (5)) / 2
nrPhi  = (1 - sqrtInteger (5)) / 2

piPhi  = (1 + sqrtInteger (-5)) / 2
niPhi  = (1 - sqrtInteger (-5)) / 2

-- | The square root of an 'Integer'.
sqrtInteger         :: Integer -> CZ
sqrtPositiveInteger :: Integer -> CZ

sqrtInteger n
    | n == 0     = zeroCyc
    | n < 0      = i * sqrtPositiveInteger (-n)
    | otherwise  = sqrtPositiveInteger n

sqrtPositiveInteger n
    | n < 1      = error "sqrtPositiveInteger needs a positive integer"
    | otherwise  = let factors = factorise n
                       factor2 = product [p^(m `div` 2) | (p,m) <- factors]
                       nn2     = product [p^(m `mod` 2) | (p,m) <- factors]
                   in case nn2 `mod` 4 of
                        1 -> fromInteger factor2        * (2 * eb nn2 + 1)
                        3 -> fromInteger factor2 * (-i) * (2 * eb nn2 + 1)                                                
                        2 -> fromInteger factor2 * sqrt2 * sqrtPositiveInteger (nn2 `div` 2)
                        _ -> fromInteger factor2 *     2 * sqrtPositiveInteger (nn2 `div` 4)

-- | The square root of a 'Rational' number.
sqrtRat :: Rational -> CZ
sqrtRat r = prodRatCyc (1 % fromInteger den) (sqrtInteger (numerator r * den))
    where
      den = denominator r


rrRat :: Rational -> Rational -> Rational -> Rational -> Rational -> CZ

rrRat       ll       lr       c         cr        rr
     = undefined 
-- | The square root of -1.
i :: CZ
i = e 4

sqrt001 = sqrtInteger (-1)
sqrt002 = sqrtInteger (-2)
sqrt003 = sqrtInteger (-3)
sqrt004 = sqrtInteger (-4)
sqrt007 = sqrtInteger (-7)
sqrt008 = sqrtInteger (-8)
sqrt011 = sqrtInteger (-11)
sqrt043 = sqrtInteger (-43)
sqrt067 = sqrtInteger (-67)
sqrt163 = sqrtInteger (-163)


sqrt023 = sqrtInteger (-23)

-- | Make a Gaussian rational; @gaussianRat p q@ is the same as @p + q * i@.
gaussianRat :: Rational -> Rational -> CZ
gaussianRat p q = fromRational p + fromRational q * i

-- | A complex number in polar form, with rational magnitude @r@ and rational angle @s@
--   of the form @r * exp(2*pi*i*s)@; @polarRat r s@ is the same as @r * e q ^ p@,
--   where @s = p/q@.
polarRat :: Rational -> Rational -> CZ
polarRat r s = fromRational r * e q ^ p
    where
      p = numerator s
      q = denominator s

-- | Complex conjugate.
conj :: CZ -> CZ
conj (CZ n mp) = mkCZ n (M.mapKeys (\k -> (n-k) `mod` n) mp)

-- | Real part of the cyclotomic number.
real :: CZ -> CZ
real z = (z + conj z) / 2



-- | Imaginary part of the cyclotomic number.
imag :: CZ -> CZ
imag z = (z - conj z) / (2*i)

imag3 :: CZ -> CZ
imag3 z = (z - conj z) / (3*i)

real3 :: CZ -> CZ
real3 z = (z + conj z) / 3

-- | Modulus squared.
modSq :: CZ -> Rational
modSq z = case toRat (z * conj z) of
            Just msq -> msq
            Nothing  -> error $ "modSq:  tried z = " ++ show z



-- Corresponds to GAP implementation.
-- Expects that convertToBase has already been done.

-- | Step 1 of cyclotomic is gcd reduction.
gcdReduce :: CZ -> CZ
gcdReduce cyc@(CZ n mp) = case gcdCyc cyc of
                                    1 -> cyc
                                    d -> CZ (n `div` d) (M.mapKeys (\k -> k `div` d) mp)

gcdCyc :: CZ -> Integer
gcdCyc (CZ n mp) = gcdList (n:M.keys mp)

-- | Step 2 of cyclotomic is reduction to a rational if possible.
tryRational :: CZ -> CZ
tryRational c
    | lenCyc c == fromIntegral phi && sqfree
        = case equalCoefficients c of
            Nothing -> c
            Just r  -> fromRational $ (-1)^(nrp `mod` 2)*r
    | otherwise
        = c
    where
      (phi,nrp,sqfree) = phiNrpSqfree (order c)

-- | Compute phi(n), the number of prime factors, and test if n is square-free.
--   We do these all together for efficiency, so we only call factorise once.
phiNrpSqfree :: Integer -> (Integer,Int,Bool)
phiNrpSqfree n = (phi,nrp,sqfree)
    where
      factors = factorise n
      phi = foldr (\p n' -> n' `div` p * (p-1)) n [p | (p,_) <- factors]
      nrp = length (factors)
      sqfree = all (<=1) [m | (_,m) <- factors]

equalCoefficients :: CZ -> Maybe Rational
equalCoefficients (CZ _ mp)
    = case ts of
        []    -> Nothing
        (x:_) -> case equal ts of
                   True  -> Just x
                   False -> Nothing
      where
        ts = M.elems mp

lenCyc :: CZ -> Int
lenCyc (CZ _ mp) = M.size $ removeZeros mp



removeZeros    ::                                    M.Map Integer Rational -> M.Map Integer Rational
replace        :: Integer -> Integer -> Integer   -> M.Map Integer Rational -> M.Map Integer Rational
convertToBase  ::                       Integer   -> M.Map Integer Rational -> M.Map Integer Rational
cyclotomic     :: Integer                         -> M.Map Integer Rational -> CZ
mkCZ           :: Integer                         -> M.Map Integer Rational -> CZ

convertToBase n mp = foldr (\(p,r) m -> replace n p r m) mp (extrPowers n)
removeZeros        = M.filter (/= 0)
cyclotomic     ord = tryReduce . tryRational . gcdReduce . CZ ord
mkCZ           ord = cyclotomic ord . removeZeros . convertToBase ord

replace n p r mp = case M.lookup r mp of
                     Nothing  -> mp
                     Just rat -> foldr (\k m -> M.insertWith (+) k (-rat) m) (M.delete r mp) (replacements n p r)

replacements n p r =     takeWhile (>= 0) [r-s,r-2*s..] ++ 
                         takeWhile (<  n) [r+s,r+2*s..]
    where s = n `div` p


-- | Step 3 of cyclotomic is base reduction
tryReduce      ::                   CZ -> CZ
reduceByPrime  :: Integer ->        CZ -> CZ
prodCyc        ::             CZ -> CZ -> CZ
sumCyc         ::             CZ -> CZ -> CZ
prodRatCyc     :: Rational       -> CZ -> CZ

eqReplacements :: Integer -> Integer -> CZ -> Maybe Rational
replacements   :: Integer -> Integer -> Integer -> [Integer]
includeMods    :: Integer -> Integer -> Integer -> [Integer]
removeExps     :: Integer -> Integer -> Integer -> [Integer]
pqPairs        ::                       Integer -> [(Integer,Integer)]
extrPowers     ::                       Integer -> [(Integer,Integer)]


tryReduce c
    = foldr reduceByPrime c squareFreeOddFactors
      where
        squareFreeOddFactors = [p | (p,m) <- factorise (order c), p > 2, m <= 1]

reduceByPrime p c@(CZ n _)
    = case sequence $ map (\r -> eqReplacements p r c) [0,p..n-p] of
        Just cfs -> CZ (n `div` p) $ removeZeros $ M.fromList $ zip [0..(n `div` p)-1] (map negate cfs)
        Nothing  -> c

eqReplacements p r (CZ n mp)
    =  case [M.findWithDefault 0 k mp | k <- replacements n p r] of
         [] -> error "eqReplacements generated empty list"
         (x:xs) | equal (x:xs) -> Just x
         _ -> Nothing




includeMods n q start = [start] 
                         ++ takeWhile (>= 0) [start-q , start-2*q ..] 
                         ++ takeWhile (< n ) [start+q , start+2*q ..]

removeExps n 2 q = concat $ map (includeMods n q) $ map ((n `div` q) *) [q `div` 2                  ..q-1]
removeExps n p q = concat $ map (includeMods n q) $ map ((n `div` q) *) [-m                         ..m  ]
                                                              where       m = (q `div` p-1) `div` 2


pqPairs n = map (\(p,k) -> (p,p^k)) (factorise n)

extrPowers n
    | n < 1      = error "extrPowers needs a postive integer"
    | otherwise  = nub $ concat $ [ [(p,r) | r <- removeExps n p q] | (p,q) <- pqPairs n]

-- | Sum of two cyclotomic numbers.
sumCyc (CZ o1 map1) (CZ o2 map2)
    = let ord = lcm o1 o2
          m1    = ord `div` o1
          m2    = ord `div` o2
          map1'   = M.mapKeys (m1*) map1
          map2'   = M.mapKeys (m2*) map2
      in                                mkCZ ord $ M.unionWith (+) map1' map2'

-- | Product of two cyclotomic numbers.
prodCyc (CZ o1 map1) (CZ o2 map2)
    = let ord = lcm o1 o2
          m1 = ord `div` o1
          m2 = ord `div` o2
      in                                mkCZ ord $ M.fromListWith (+)
             [((m1*e1+m2*e2) `mod` ord,c1*c2) | (e1,c1) <- M.toList map1, (e2,c2) <- M.toList map2]

-- | Product of a rational number and a cyclotomic number.
prodRatCyc 0 ___________ = zeroCyc
prodRatCyc r (CZ ord mp) = CZ ord $ M.map (r*) mp

zeroCyc                  = CZ (1) (M.empty)

-- | Additive identity.

-- | Additive inverse.

-- | Multiplicative inverse.
zeroCyc      :: CZ
aInv_1_CZ    :: CZ -> CZ
mInv_2_CZ    :: CZ -> CZ

mInv_2_CZ  z = prodRatCyc (2 / modSq z) (conj z)
mInv_3_CZ  z = prodRatCyc (3 / modSq z) (conj z)
mInv_6_CZ  z = prodRatCyc (6 / modSq z) (conj z)
mInv_12_CZ  z = prodRatCyc (12/ modSq z) (conj z)

mInv_23_CZ  z = prodRatCyc (23 / modSq z) (conj z)
mInv_24_CZ  z = prodRatCyc (24 / modSq z) (conj z)

aInv_1_CZ  z = prodRatCyc (-1)          (     z)

-- | Is the cyclotomic a real number?
isReal         :: CZ -> Bool
isRat          :: CZ -> Bool
isGaussianRat  :: CZ -> Bool
isEisenstRat   :: CZ -> Bool
toComplex2     :: CZ ->       Complex Double
toReal         :: CZ -> Maybe         Double
toRat          :: CZ -> Maybe         Rational

isReal c       = (==) c (conj c)
isRat (CZ 1 _) = True
isRat _        = False
isGaussianRat c = (&&) (isRat (real c))
                       (isRat (imag c))

isEisenstRat c = undefined

-- | Is the cyclotomic a rational?

-- | Is the cyclotomic a Gaussian rational?

-- | Export as an inexact complex number.

toComplex2 c = sum [fromRational r * en^p | (p,r) <- M.toList (coeffs c)]
    where en = exp (0 :+ 2*pi/(1*n))
          n = fromIntegral (order c)

toComplex3 c = sum [fromRational r * en^p | (p,r) <- M.toList (coeffs c)]
    where en = exp (0 :+ 2*pi/(3*n))
          n = fromIntegral (order c)

toComplex23 c = sum [fromRational r * en^p | (p,r) <- M.toList (coeffs c)]
    where en = exp (0 :+ 2*pi/(24*n))
          n = fromIntegral (order c)

-- | Export as an inexact real number if possible.
toReal c            | isReal c          = Just $ realPart (toComplex2 c)
                    | otherwise         = Nothing
-- | Return an exact rational number if possible.
toRat (CZ 1 mp)     | mp == M.empty     = Just 0
                    | otherwise         = M.lookup 0 mp
toRat _ = Nothing

-- | Sine function with argument in degrees.
sinDeg :: Rational -> CZ
cosDeg :: Rational -> CZ

sinDeg d = let n = d / 360
               nm = abs (numerator   n)
               dn =      denominator n
               a = e dn^nm
           in fromRational(signum d) * (a - conj a) / (2*i)

-- | Cosine function with argument in degrees.
cosDeg d = let n = d / 360
               nm = abs (numerator   n)
               dn =      denominator n
               a = e dn^nm
           in (a + conj a) / 2

gcdList :: [Integer] -> Integer
gcdList [] = error "gcdList called on empty list"
gcdList (n:ns) = foldr gcd n ns

equal :: Eq a => [a] -> Bool
equal [] = True
equal [_] = True
equal (x:y:ys) = x == y && equal (y:ys)



-- apollonian outer equation:

-- l b c d r x y z
-- 0 0 1 1 1 2 2 3

apd3 l b c d r x y z = 
 let
     l' =              (4*r - l)
     b' = negate 2 *        l'       +  b
     c' = negate 2 *        l'       +  c + 1
     d' = negate 2 *        l'       +  d
     r' =              (4*  l' - r)
     x' = negate 2 *        r'       +  x
     y' = negate 2 *        r'       +  y
     z' = negate 2 *        r'       +  z
 in
     return (l', b', c', d', r', x', y', z')



-----------------------------------------------------------------------------------------------------------
-- inversion code from Bird
-----------------------------------------------------------------------------------------------------------

findBS    
       (u,v)  (r,s)  f      z
        
               
                       
     | u > r    ||   v < s         =  []
     | v - s    <=   r - u         =  rfind  (bsearch  (\x  ->  f(x,q))  (u-1,r+1)  z)
     |       otherwise             =  cfind  (bsearch  (\y  ->  f(p,y))  (s-1,v+1)  z)
       where
              p                    = (  u+r)   `div`     2
              q                    = (  v+s)   `div`     2
              rfind  p =    (if  f( p,q)  ==  z  
                             then ( p,q):  findBS  (u,v)  (p-1,q+1)      f  z
                             else          findBS  (u,v)  (p  ,q+1)      f  z
                             )  ++         findBS  (p+1, q-1)  (r,s)     f  z

              cfind  q =    findBS  (u,v)  (p-1,q+1)  f  z
                                   ++ (if  f(p,q)  ==  z  then  (p,q):  findBS  (p+1, q-1)  (r,s)  f  z
                                        else  findBS  (p+1,  q)  (r,s)  f  z
                                        )


{-# INLINE findBS #-}
{-# INLINE bsearch #-}
{-# INLINE invert #-}
{-# INLINE birdFactor #-}


invert :: Integral a => ((a, a) -> a) -> a -> [(a, a)]
findBS :: (Integral a, Ord a1) => (a, a) -> (a, a) -> ((a, a) -> a1) -> a1 -> [(a, a)]
bsearch :: (Integral a, Ord a1) => (a -> a1) -> (a, a) -> a1 -> a

invert  f  z      =    findBS    (0,m)  (n,0)
                                                            f    
                                                                                z
     where
               m    =    bsearch   (\y  ->  f  (0,y))       (negate  1,  z+1)       
                                                                                z
               n    =    bsearch   (\x  ->  f  (x,0))       (negate  1,  z+1)   z
                                   



bsearch grow  (a, b) z
                    | a + 1 == b          =  a
                    | grow m <= z         =  bsearch grow (m, b) z
                    | otherwise           =  bsearch grow (a, m) z
          where m   = mid a b
                mid l r = (l + r) `div` 2


--  where we extend f with ﬁctitious values f (0, − 1) = 0 and f ( − 1, 0) = 0.
--  This version of invert takes about 2 log z + m + n evaluations of f in the
--  worst case and 2 log z + m min n in the best case. Since m or n may be
--  substantially less than z, for example when f (x, y) = 2
--  x
--  + 3
--  y
--  , we can end  up with an algorithm that takes only O(log z) steps in the worst case.


{-# SPECIALIZE birdFactor :: Int -> [(Int, Int)] #-}

-- factorise :: Integer -> [(Integer, Int)]
birdFactor :: Integral a => a -> [(a, a)]
birdFactor n = invert (\(x,y) -> x*y) n


q1 n = invert (\(x,y) ->  6*x*x  +    x*y +   y*y) n
q2 n = invert (\(x,y) ->  12*x*x + 13*x*y + 4*y*y) n
q3 n = invert (\(x,y) ->  18*x*x + 25*x*y + 9*y*y) n
