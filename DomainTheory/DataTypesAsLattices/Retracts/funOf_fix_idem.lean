/-ai
If F is Scott continuous and sends retracts to retracts, then the least fixed point of F is idempotent under application.

The iterates of F from the empty set increase with the stage. Each iterate is idempotent under application because it is a retract, and application of an iterate distributes over the directed union of the applications of the iterates. In one direction, membership in the double application is membership in the application of the union of the iterates to the union of their applications. A finite piece and a later iterate are bounded by a common stage, the μ-law moves the membership into the double application at that stage, and idempotence returns a single application, which lies in the union defining the least fixed point. In the other direction, membership in some iterate is restored to a double application by idempotence, and monotonicity of application in each argument returns it to the double application of the two unions.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















































theorem funOf_fix_idem {F : Pomega → Pomega} (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a)) (x : Pomega) :
    funOf (fix F) (funOf (fix F) x) = funOf (fix F) x := by
  have hchain : ∀ n m, n ≤ m → iterateBot F n ⊆ iterateBot F m :=
    chain_mono (iterateBot F) (iterateBot_mono hf)
  have hidem : ∀ n, funOf (iterateBot F n) (funOf (iterateBot F n) x) =
      funOf (iterateBot F n) x :=
    fun n => retract_app (iterates_areRetracts hret n) x
  have hcl : ∀ n,
      funOf (iterateBot F n) (⋃ m, funOf (iterateBot F m) x) =
        ⋃ m, funOf (iterateBot F n) (funOf (iterateBot F m) x) :=
    fun n => chain_lemma (funOf_isScottContinuous (iterateBot F n))
      (fun m => funOf (iterateBot F m) x)
      (fun m => funOf_monotone_left (iterateBot_mono hf m) x)
  apply subset_antisymm
  · intro k hk
    have hk' : k ∈ funOf (⋃ n, iterateBot F n)
        (⋃ m, funOf (iterateBot F m) x) := by
      simpa [fix, funOf_iUnion] using hk
    obtain ⟨n, hn, hp⟩ := hk'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    have : k ∈ funOf (iterateBot F i) (⋃ m, funOf (iterateBot F m) x) :=
      ⟨n, hn, hi⟩
    have : k ∈ ⋃ m, funOf (iterateBot F i) (funOf (iterateBot F m) x) := by
      rwa [hcl i] at this
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp this
    let N := max i j
    have hij : funOf (iterateBot F i) (funOf (iterateBot F j) x) ⊆
        funOf (iterateBot F N) (funOf (iterateBot F N) x) :=
      mu_law (hchain i N (le_max_left i j))
        (funOf_monotone_left (hchain j N (le_max_right i j)) x)
    have : k ∈ funOf (iterateBot F N) x := by
      have : k ∈ funOf (iterateBot F N) (funOf (iterateBot F N) x) := hij hj
      rwa [hidem N] at this
    simpa [fix, funOf_iUnion] using Set.mem_iUnion.mpr ⟨N, this⟩
  · intro k hk
    have : k ∈ ⋃ n, funOf (iterateBot F n) x := by
      simpa [fix, funOf_iUnion] using hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp this
    have : k ∈ funOf (iterateBot F n) (funOf (iterateBot F n) x) := by
      rw [hidem n]
      exact hkn
    have : k ∈ funOf (iterateBot F n) (⋃ m, funOf (iterateBot F m) x) :=
      funOf_monotone_right _ (Set.subset_iUnion (fun m => funOf (iterateBot F m) x) n) this
    have : k ∈ funOf (⋃ i, iterateBot F i) (⋃ m, funOf (iterateBot F m) x) :=
      funOf_monotone_left (Set.subset_iUnion (iterateBot F) n) _ this
    simpa [fix, funOf_iUnion] using this

end DomainTheory.DataTypesAsLattices
