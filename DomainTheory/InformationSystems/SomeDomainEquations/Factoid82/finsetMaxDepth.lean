module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst10
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst17
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst18
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.maxDepthInsert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst31
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.foldl_list_le_of_mem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.foldr_max_le_of_forall
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.foldr_max_lt_of_forall
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamInputUnion
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamOutputUnion
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.listToFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamFunFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamInputUnion
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamOutputUnion
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_listToFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.rawDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.rawDepth_funTok_gt_left
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.rawDepth_funTok_gt_right

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]
variable (A : InfoSys α)

def finsetMaxDepth (u : Finset (RawLamToken α)) : ℕ :=
  Multiset.foldr (maxDepthInsert (α := α)) 0 u.1

theorem finsetMaxDepth.listToFinset_le (u : List (RawLamToken α)) :
    finsetMaxDepth (listToFinset u) ≤
      List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u := by
  simp only [finsetMaxDepth]
  exact foldr_max_le_of_forall fun t ht =>
    foldl_list_le_of_mem ((mem_listToFinset).1 (Finset.mem_def.2 ht))

theorem finsetMaxDepth.list_lt_funTok (u v : List (RawLamToken α)) :
    finsetMaxDepth (listToFinset u) < rawDepth (.funTok u v) := by
  have h1 := finsetMaxDepth.listToFinset_le u
  have h2 : List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u ≤
      Nat.max (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u)
        (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v) :=
    Nat.le_max_left _ _
  simp only [rawDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) (Nat.lt_add_of_pos_left (Nat.succ_pos 0))

omit [DecidableEq α] in

theorem le_finsetMaxDepth_of_mem {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (ht : t ∈ u) : rawDepth t ≤ finsetMaxDepth u := by
  simp only [finsetMaxDepth]
  have ht' : t ∈ u.1 := Finset.mem_def.1 ht
  revert ht'
  refine Multiset.induction_on u.1 ?_ ?_
  · intro ht'; cases ht'
  · intro a s ih ht'
    simp only [Multiset.mem_cons] at ht'
    simp only [Multiset.foldr_cons, maxDepthInsert]
    rcases ht' with rfl | ht'
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih ht') (Nat.le_max_right _ _)

theorem finsetMaxDepth.inputUnion_lt {u : Finset (RawLamToken α)}
    {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (hs : s ⊆ lamFunFinset u) (hfun : lamFunFinset u ≠ ∅) :
    finsetMaxDepth (lamInputUnion s) < finsetMaxDepth u := by
  obtain ⟨p0, hp0⟩ := Finset.nonempty_of_ne_empty hfun
  have htok0 : .funTok p0.1 p0.2 ∈ u := mem_lamFunFinset.1 hp0
  have hpos : 0 < finsetMaxDepth u := by
    have hraw : 0 < rawDepth (.funTok p0.1 p0.2) := by
      simp only [rawDepth]
      exact Nat.add_pos_left (Nat.succ_pos 0) _
    exact Nat.lt_of_lt_of_le hraw (le_finsetMaxDepth_of_mem htok0)
  refine foldr_max_lt_of_forall (s := (lamInputUnion s).1) hpos ?_
  intro t ht
  have ht' : t ∈ lamInputUnion s := Finset.mem_def.2 ht
  rcases (mem_lamInputUnion).1 ht' with ⟨p, hp, htp⟩
  have htok : .funTok p.1 p.2 ∈ u := mem_lamFunFinset.1 (hs hp)
  exact Nat.lt_of_lt_of_le
    (rawDepth_funTok_gt_left ((mem_listToFinset).1 htp))
    (le_finsetMaxDepth_of_mem htok)

theorem finsetMaxDepth.outputUnion_lt {u : Finset (RawLamToken α)}
    {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (hs : s ⊆ lamFunFinset u) (hfun : lamFunFinset u ≠ ∅) :
    finsetMaxDepth (lamOutputUnion s) < finsetMaxDepth u := by
  obtain ⟨p0, hp0⟩ := Finset.nonempty_of_ne_empty hfun
  have htok0 : .funTok p0.1 p0.2 ∈ u := mem_lamFunFinset.1 hp0
  have hpos : 0 < finsetMaxDepth u := by
    have hraw : 0 < rawDepth (.funTok p0.1 p0.2) := by
      simp only [rawDepth]
      exact Nat.add_pos_left (Nat.succ_pos 0) _
    exact Nat.lt_of_lt_of_le hraw (le_finsetMaxDepth_of_mem htok0)
  refine foldr_max_lt_of_forall (s := (lamOutputUnion s).1) hpos ?_
  intro t ht
  have ht' : t ∈ lamOutputUnion s := Finset.mem_def.2 ht
  rcases (mem_lamOutputUnion).1 ht' with ⟨p, hp, htp⟩
  have htok : .funTok p.1 p.2 ∈ u := mem_lamFunFinset.1 (hs hp)
  exact Nat.lt_of_lt_of_le
    (rawDepth_funTok_gt_right ((mem_listToFinset).1 htp))
    (le_finsetMaxDepth_of_mem htok)

theorem finsetMaxDepth.list_lt_funTok_out (u v : List (RawLamToken α)) :
    finsetMaxDepth (listToFinset v) < rawDepth (.funTok u v) := by
  have h1 := finsetMaxDepth.listToFinset_le v
  have h2 : List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v ≤
      Nat.max (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u)
        (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v) :=
    Nat.le_max_right _ _
  simp only [rawDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) (Nat.lt_add_of_pos_left (Nat.succ_pos 0))

theorem finsetMaxDepth.of_mem_funTok {u : Finset (RawLamToken α)}
    {xs ys : List (RawLamToken α)} (h : .funTok xs ys ∈ u) :
    finsetMaxDepth (listToFinset xs) < finsetMaxDepth u ∧
      finsetMaxDepth (listToFinset ys) < finsetMaxDepth u :=
  ⟨Nat.lt_of_lt_of_le (finsetMaxDepth.list_lt_funTok xs ys) (le_finsetMaxDepth_of_mem h),
    Nat.lt_of_lt_of_le (finsetMaxDepth.list_lt_funTok_out xs ys) (le_finsetMaxDepth_of_mem h)⟩

end InfoSys

end DomainTheory.InformationSystems
