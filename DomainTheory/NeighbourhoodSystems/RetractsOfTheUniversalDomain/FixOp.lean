module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.FixedNbhdFinitaryOrder
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Examples_8_4

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}

theorem eq_bot_of_fixed_constMap_bot {y : E.Element}
    (hy : (constMap E E.bot).toElementMap y = y) : y = E.bot := by
  rw [toElementMap_constMap] at hy
  exact hy.symm

instance uniqueFixedConstMapBot :
    Unique {y : E.Element // (constMap E E.bot).toElementMap y = y} where
  default := ⟨E.bot, toElementMap_constMap E.bot E.bot⟩
  uniq := fun ⟨_y, hy⟩ => Subtype.ext (eq_bot_of_fixed_constMap_bot hy)

def finitaryWitnessEquivBot (E : NeighborhoodSystem α) :
    {y : E.Element // (constMap E E.bot).toElementMap y = y} ≃o unitSys.Element where
  toFun _ := default
  invFun _ := default
  left_inv a := (Unique.eq_default a).symm
  right_inv b := (Unique.eq_default b).symm
  map_rel_iff' := by
    intro a b
    have hab : a = b := (Unique.eq_default a).trans (Unique.eq_default b).symm
    exact iff_of_true (le_refl default) (le_of_eq hab)

def fixOp (t : ApproximableMap (funSpace E E) (funSpace E E)) : ApproximableMap E E :=
  toApproxMap t.fixElement

def tOp (t : ApproximableMap (funSpace E E) (funSpace E E)) (a : ApproximableMap E E) :
    ApproximableMap E E :=
  toApproxMap (t.toElementMap (toFilter a))

abbrev Fix (a : ApproximableMap E E) := {y : E.Element // a.toElementMap y = y}

theorem constMap_bot_le_idMap (E : NeighborhoodSystem α) :
    constMap E E.bot ≤ idMap E := by
  rintro X Z hr
  rw [constMap_rel, mem_bot] at hr
  obtain ⟨hX, rfl⟩ := hr
  exact ⟨hX, E.master_mem, E.sub_master hX⟩

theorem isRetraction_constMap_bot (E : NeighborhoodSystem α) :
    Retraction (constMap E E.bot) := by
  constructor
  show (constMap E E.bot).comp (constMap E E.bot) = constMap E E.bot
  apply ApproximableMap.ext
  intro X Z
  simp only [comp_rel, constMap_rel, mem_bot]
  constructor
  · rintro ⟨Y, ⟨hX, rfl⟩, -, hZ⟩
    exact ⟨hX, hZ⟩
  · rintro ⟨hX, hZ⟩
    exact ⟨E.master, ⟨hX, rfl⟩, E.master_mem, hZ⟩

theorem isProjection_constMap_bot (E : NeighborhoodSystem α) :
    IsProjection (constMap E E.bot) :=
  ⟨isRetraction_constMap_bot E, constMap_bot_le_idMap E⟩

theorem isFinitaryProjection_constMap_bot (E : NeighborhoodSystem α) :
    FinitaryProjection (constMap E E.bot) :=
  ⟨⟨isProjection_constMap_bot E, Unit, unitSys, ⟨finitaryWitnessEquivBot E⟩⟩⟩

theorem iterElem_succ' (t : ApproximableMap (funSpace E E) (funSpace E E)) (n : ℕ) :
    t.iterElem (n + 1) = t.toElementMap (t.iterElem n) := by
  show (t.comp (t.iterMap n)).toElementMap (funSpace E E).bot = t.toElementMap (t.iterElem n)
  rw [toElementMap_comp]
  rfl

theorem iterElem_zero' (t : ApproximableMap (funSpace E E) (funSpace E E)) :
    t.iterElem 0 = (funSpace E E).bot := by
  show (idMap (funSpace E E)).toElementMap (funSpace E E).bot = (funSpace E E).bot
  rw [toElementMap_idMap]

theorem rel_master_of_mem (f : ApproximableMap E E) {X : Set α} (hX : E.mem X) :
    f.rel X E.master :=
  f.mono f.master_rel (E.sub_master hX) subset_rfl hX E.master_mem

theorem tOp_fixOp (t : ApproximableMap (funSpace E E) (funSpace E E)) :
    tOp t (fixOp t) = fixOp t := by
  show toApproxMap (t.toElementMap (toFilter (toApproxMap t.fixElement))) = toApproxMap t.fixElement
  rw [toFilter_toApproxMap, toElementMap_fixElement]

theorem tOp_toApproxMap (t : ApproximableMap (funSpace E E) (funSpace E E))
    (φ : (funSpace E E).Element) : tOp t (toApproxMap φ) = toApproxMap (t.toElementMap φ) := by
  unfold tOp
  rw [toFilter_toApproxMap]

theorem toApproxMap_bot_eq_constMap (E : NeighborhoodSystem α) :
    toApproxMap (funSpace E E).bot = constMap E E.bot := by
  apply ApproximableMap.ext
  intro X Y
  simp only [toApproxMap_rel, mem_bot, constMap_rel]
  constructor
  · intro h
    have hcb : constMap E E.bot ∈ step X Y := by rw [h]; trivial
    rwa [mem_step, constMap_rel, mem_bot] at hcb
  · rintro ⟨hX, rfl⟩
    exact Set.eq_univ_of_forall fun f => rel_master_of_mem f hX

theorem isFinitaryProjection_fixOp (t : ApproximableMap (funSpace E E) (funSpace E E))
    (ht : ∀ a, FinitaryProjection a → FinitaryProjection (tOp t a)) :
    FinitaryProjection (fixOp t) := by
  have hchain : ∀ n, FinitaryProjection (toApproxMap (t.iterElem n)) := by
    intro n
    induction n with
    | zero =>
      rw [iterElem_zero', toApproxMap_bot_eq_constMap]
      exact isFinitaryProjection_constMap_bot E
    | succ k ih =>
      rw [iterElem_succ', ← tOp_toApproxMap t (t.iterElem k)]
      exact ht _ ih
  have hsub : ∀ n, subFilter (t.iterElem n) = t.iterElem n := by
    intro n
    apply toApproxMap_injective
    rw [toApproxMap_subFilter]
    exact sub_eq_self_of_isFinitaryProjection (hchain n)
  have hdir : ∀ i j : ℕ, ∃ k, t.iterElem i ≤ t.iterElem k ∧ t.iterElem j ≤ t.iterElem k :=
    fun i j => ⟨max i j, iterElem_mono t (le_max_left i j), iterElem_mono t (le_max_right i j)⟩
  have hdirSub : ∀ i j : ℕ, ∃ k, subFilter (t.iterElem i) ≤ subFilter (t.iterElem k) ∧
      subFilter (t.iterElem j) ≤ subFilter (t.iterElem k) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdir i j
    refine ⟨k, ?_, ?_⟩
    · rw [hsub i, hsub k]; exact hik
    · rw [hsub j, hsub k]; exact hjk
  have hEq : t.fixElement = iSupDirected t.iterElem hdir := by
    apply NeighborhoodSystem.Element.ext
    intro Z
    rw [mem_fixElement, mem_iSupDirected]
    simp_rw [mem_iterElem]
  have hkey : subFilter t.fixElement = t.fixElement := by
    rw [hEq, subFilter_iSupDirected t.iterElem hdir hdirSub]
    apply NeighborhoodSystem.Element.ext
    intro Z
    rw [mem_iSupDirected, mem_iSupDirected]
    simp_rw [hsub]
  show FinitaryProjection (toApproxMap t.fixElement)
  apply isFinitaryProjection_of_sub_eq_self
  rw [← toApproxMap_subFilter, hkey]

theorem fixedDomain_fixOp_iso_T (t : ApproximableMap (funSpace E E) (funSpace E E))
    (ht : ∀ a, FinitaryProjection a → FinitaryProjection (tOp t a))
    (T : ApproximableMap E E → Σ β : Type, NeighborhoodSystem β)
    (hT : ∀ a, FinitaryProjection a → Nonempty (Fix (tOp t a) ≃o (T a).2.Element)) :
    Nonempty (Fix (fixOp t) ≃o (T (fixOp t)).2.Element) := by
  have h := hT (fixOp t) (isFinitaryProjection_fixOp t ht)
  rwa [tOp_fixOp] at h

theorem fixedNbhd_fixOp_subsystem (t : ApproximableMap (funSpace E E) (funSpace E E))
    (ht : ∀ a, FinitaryProjection a → FinitaryProjection (tOp t a))
    {a : ApproximableMap E E} (ha : FinitaryProjection a) (hpre : tOp t a ≤ a) :
    fixedNbhd (fixOp t) ◁ fixedNbhd a := by
  have hpre' : toApproxMap (t.toElementMap (toFilter a)) ≤ toApproxMap (toFilter a) := by
    show tOp t a ≤ toApproxMap (toFilter a)
    rw [toApproxMap_toFilter]
    exact hpre
  have h1 : t.toElementMap (toFilter a) ≤ toFilter a := by
    have hiff := (funSpaceEquiv E E).le_iff_le
      (x := t.toElementMap (toFilter a)) (y := toFilter a)
    rw [funSpaceEquiv_apply, funSpaceEquiv_apply] at hiff
    exact hiff.mp hpre'
  have h2 : t.fixElement ≤ toFilter a := fixElement_le_of_toElementMap_le t h1
  have hle : fixOp t ≤ a := by
    show toApproxMap t.fixElement ≤ a
    rw [← toApproxMap_toFilter a]
    exact toApproxMap_monotone h2
  exact (isFinitaryProjection_le_iff_fixedNbhd_subsystem
    (isFinitaryProjection_fixOp t ht) ha).mp hle

end Exercise823

end DomainTheory.NeighbourhoodSystems
