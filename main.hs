import Data.List
import Data.Maybe

type Nand = String
type Or = String
type ProofStep = ([Nand],Or,Nand)
type Cache = [(Nand,Proof)]

data Proof = Axiom Nand | Impl [Proof] Or Nand deriving (Show)

instance Eq Proof where
    (Axiom a) == (Axiom b) = a == b
    (Impl _ _ a) == (Impl _ _ b) = a == b
    _ == _ = False

instance Ord Proof where
    (Axiom a) `compare` (Axiom b) = a `compare` b
    (Impl _ _ a) `compare` (Impl _ _ b) = a `compare` b

step_helper :: [Nand] -> Or -> Nand
step_helper [] [] = []
step_helper (n:ncs) (o:oc) = union (delete o n) (step_helper ncs oc)

match_helper :: [Nand] -> Or -> Bool
match_helper [] [] = True
match_helper [] _ = False
match_helper _ [] = False
match_helper (n:ncs) (o:oc) = elem o n && match_helper ncs oc

match :: [Nand] -> Or -> Bool
match ncs oc =
	let flat = concat ncs
	in if all (\o -> elem o flat) oc
		 then any (match_helper ncs) (permutations oc)
		 else False

find_matching_or_perm :: [Nand] -> Or -> Or
find_matching_or_perm ncs oc = fromJust (find (match_helper ncs) (permutations oc))

-- match n NANDs with OR of length n, returning the resulting NAND
step :: [Nand] -> Or -> Cache -> Cache
step ncs oc cache = add_to_cache new_nand (Impl (map (\n -> get_from_cache n cache) ncs) oc new_nand) cache
										where
											new_nand = sort$step_helper ncs (find_matching_or_perm ncs oc)

-- get all subsets of NANDs matching OR
-- return only subsets containing at least one new NAND-clause (x4 performance)
matching_nand_subsets :: [Nand] -> Or -> [Nand] -> [[Nand]]
matching_nand_subsets ncs oc new =
	let eligible = filter (overlaps oc) ncs; new_eligible = filter (overlaps oc) new
	in filter (\n -> match n oc) (extend (n_subsets ((length oc)-1) eligible) new_eligible)

-- get all possible resulting NANDs from a set of NANDs and an OR
deduce_with_or :: [Nand] -> Or -> Int -> [Nand] -> Cache -> Cache
deduce_with_or ncs oc k new cache | k == 0 = result
																	| otherwise = filter (\n -> length (fst n) <= k) result
																	where
																		nand_subsets = matching_nand_subsets ncs oc new
																		result = foldr (\n -> \c -> step n oc c) cache nand_subsets

-- get all possible resulting NANDs from a set of NANDs and ORs
deduce_once :: [Nand] -> [Or] -> Int -> [Nand] -> Cache -> (Cache,[Nand])
deduce_once ncs ocs k new cache =
	let new_cache = foldr (\oc -> \c -> deduce_with_or ncs oc k new c) cache ocs
	in (sort$remove_duplicates (new_cache ++ cache), remove_duplicates (map fst new_cache) \\ ncs)

deduce_helper :: [Nand] -> [Or] -> Int -> [Nand] -> Cache -> Proof
deduce_helper ncs ocs k new cache =
	let
		(result, newest) = deduce_once ncs ocs k new cache
		proof = find contradiction (map snd cache)
	in
		if
			result /= cache
		then
			if
				isNothing proof
			then
				deduce_helper (map fst result) ocs k newest result
			else
				fromJust proof
		else
			error "No contradictions!"

contradict :: [Nand] -> [Or] -> Int -> Proof
contradict ncs ocs k =
	let
		nands = sort (map sort ncs)
		ors = sort (map sort ocs)
		axioms = foldr (\n -> \cache -> add_to_cache n (Axiom n) cache) [] ncs
	in
		deduce_helper nands ors k nands axioms

-- REFUTATION

{-
refute_helper :: [Nand] -> [Or] -> Int -> [Nand] -> [Nand]
refute_helper ncs ocs k new =
	let (result, newest)  = deduce_once ncs ocs k new
	in if result == ncs || elem "" result then result else refute_helper result ocs k newest

refute :: [Nand] -> [Or] -> Int -> [Nand]
refute ncs ocs k =
	let nands = sort (map sort ncs); ors = sort (map sort ocs)
	in refute_helper nands ors k nands

-- PROOF

step_with_or :: [Proof] -> Or -> Int -> [Proof] -> [Proof]
step_with_or ps oc k new | k == 0 = result
												 | otherwise = filter (\n -> length (concl n) <= k) result
												 where
												 	 proof_subsets = filter
												 	 result = map (\p -> proof_step p oc) (matching_nand_subsets nands oc new)

step_once :: [Proof] -> [Or] -> Int -> [Proof] -> ([Proof],[Proof])
step_once ps ocs k new =
	let newest = concat (map (\el -> step_with_or ps ocs k new) ocs)
	in (sort$remove_duplicates (ps ++ newest), remove_duplicates newest \\ ps)

contradict_helper :: [Proof] -> [Or] -> Int -> [Proof] -> Proof
contradict_helper ps ocs k new =
	let (proofs, newest) = step_once ps ocs k new ; contradiction = find contradiction proofs
	in if isNothing contradiction
		 then contradict_helper proofs ocs k newest
		 else fromJust contradiction

contradict :: [Nand] -> [Or] -> Int -> Proof
contradict nc oc k =
	let nands = sort (map sort ncs); ors = sort (map sort ocs)
	in contradict_helper nands ors k nands
-}

-- PROOF UTIL

contradiction :: Proof -> Bool
contradiction p = concl p == ""

concl :: Proof -> Nand
concl (Axiom c) = c
concl (Impl _ _ c) = c

-- UTIL

overlaps :: Eq a => [a] -> [a] -> Bool
overlaps nc oc = intersect nc oc /= []

extend :: Eq a => [[a]] -> [a] -> [[a]]
extend xss ys = [(y:xs) | y <- ys, xs <- xss ]

n_subsets :: Int -> [a] -> [[a]]
n_subsets n xs =
	let l = length xs
  in if n > l then [] else n_subsets xs !! (l-n)
 	where
   	n_subsets [] = [[[]]]
   	n_subsets (x:xs) = let next = n_subsets xs
                       in zipWith (++) ([]:next) (map (map (x:)) next ++ [[]])

remove_duplicates :: Eq a => [a] -> [a]
remove_duplicates [] = []
remove_duplicates (x:xs) | elem x xs = remove_duplicates xs
              					 | otherwise = (x:remove_duplicates xs)

get_from_cache :: Nand -> Cache -> Proof
get_from_cache n [] = error "NAND not found"
get_from_cache n ((m,p):ms) | n == m = p
														| otherwise = get_from_cache n ms

add_to_cache :: Nand -> Proof -> Cache -> Cache
add_to_cache n p ms | is_in_cache n ms = ms
										| otherwise = ((n,p):ms)

is_in_cache :: Nand -> Cache -> Bool
is_in_cache n ms = any (\m -> n == fst m) ms
