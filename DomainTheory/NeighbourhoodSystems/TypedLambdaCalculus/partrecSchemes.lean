module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.lamArg
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.fixMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.PartrecLam
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)

def evalAt (z : 𝒩.Element) : ApproximableMap (funSpace 𝒩 N) N :=
  (evalMap 𝒩 N).comp (paired (idMap (funSpace 𝒩 N)) (constMap (funSpace 𝒩 N) z))

def rfindZeroPred {n : ℕ} (f : List.Vector ℕ (n + 1) → ℕ) (v : List.Vector ℕ n) : ℕ →. Bool :=
  fun k => Part.some (decide (f (k ::ᵥ v) = 0))

theorem evalAt_apply (z : 𝒩.Element) (φ : (funSpace 𝒩 N).Element) :
    (evalAt z).toElementMap φ = (toApproxMap φ).toElementMap z := by
  rw [evalAt, toElementMap_comp, toElementMap_paired, toElementMap_idMap, toElementMap_constMap,
    evalMap_apply]

theorem toApproxMap_bot (z : 𝒩.Element) :
    (toApproxMap ((funSpace 𝒩 N).bot)).toElementMap z = N.bot := by
  refine le_antisymm ?_ (N.bot_le _)
  have h2 := (funSpaceEquiv 𝒩 N).monotone
    ((funSpace 𝒩 N).bot_le ((funSpaceEquiv 𝒩 N).symm (constMap 𝒩 N.bot)))
  rw [OrderIso.apply_symm_apply, funSpaceEquiv_apply] at h2
  have h3 := (le_iff_toElementMap_le.mp h2) z
  rwa [toElementMap_constMap] at h3

section Rfind
variable (φf : ApproximableMap 𝒩 N)

def findBody : ApproximableMap (prod (funSpace 𝒩 N) 𝒩) N :=
  (cond N).comp
    (paired (zeroMap.comp (φf.comp (proj₁ (funSpace 𝒩 N) 𝒩)))
      (paired ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩))
        ((evalMap 𝒩 N).comp
          (paired (proj₀ (funSpace 𝒩 N) 𝒩)
            ((push N).comp
              (paired (succMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
                ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩))))))))

def findOp : ApproximableMap (funSpace 𝒩 N) (funSpace 𝒩 N) := curry (findBody φf)

def searchMap : ApproximableMap 𝒩 N := toApproxMap (findOp φf).fixElement

def findMap : ApproximableMap 𝒩 N :=
  (searchMap φf).comp ((push N).comp (paired (constMap 𝒩 (natElem 0)) (idMap 𝒩)))

theorem findBody_apply (k : (funSpace 𝒩 N).Element) (z : 𝒩.Element) :
    (findBody φf).toElementMap (pair k z) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (φf.toElementMap z))
          (pair ((head N).toElementMap z)
            ((toApproxMap k).toElementMap
              ((push N).toElementMap
                (pair (succMap.toElementMap ((head N).toElementMap z))
                  ((tail N).toElementMap z)))))) := by
  rw [findBody, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

theorem findOp_iterElem_zero : (findOp φf).iterElem 0 = (funSpace 𝒩 N).bot := by
  rw [iterElem_eq_iterate, Function.iterate_zero_apply]

theorem iterVal_succ (m : ℕ) (z : 𝒩.Element) :
    (toApproxMap ((findOp φf).iterElem (m + 1))).toElementMap z =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (φf.toElementMap z))
          (pair ((head N).toElementMap z)
            ((toApproxMap ((findOp φf).iterElem m)).toElementMap
              ((push N).toElementMap
                (pair (succMap.toElementMap ((head N).toElementMap z))
                  ((tail N).toElementMap z)))))) := by
  have h1 : (findOp φf).iterElem (m + 1) = (findOp φf).toElementMap ((findOp φf).iterElem m) := by
    rw [iterElem_eq_iterate, iterElem_eq_iterate, Function.iterate_succ', Function.comp_apply]
  rw [h1]
  have hval := toElementMap_curry_apply (findBody φf) ((findOp φf).iterElem m) z
  rw [← findOp] at hval
  rw [hval, findBody_apply]

theorem findMap_vecElem {n : ℕ} (v : List.Vector ℕ n) :
    (findMap φf).toElementMap (vecElem v) = (searchMap φf).toElementMap (vecElem (0 ::ᵥ v)) := by
  rw [findMap, toElementMap_comp, toElementMap_comp, toElementMap_paired, toElementMap_constMap,
    toElementMap_idMap, push_natElem_vecElem]

theorem searchMap_rec (z : 𝒩.Element) :
    (searchMap φf).toElementMap z =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (φf.toElementMap z))
          (pair ((head N).toElementMap z)
            ((searchMap φf).toElementMap
              ((push N).toElementMap
                (pair (succMap.toElementMap ((head N).toElementMap z))
                  ((tail N).toElementMap z)))))) := by
  have hfix : (findOp φf).toElementMap (findOp φf).fixElement = (findOp φf).fixElement :=
    toElementMap_fixElement (findOp φf)
  have hval := toElementMap_curry_apply (findBody φf) (findOp φf).fixElement z
  rw [← findOp, hfix] at hval
  rw [searchMap, hval, findBody_apply]

theorem searchMap_step_found {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n) (k : ℕ)
    (h0 : f (k ::ᵥ v) = 0) :
    (searchMap φf).toElementMap (vecElem (k ::ᵥ v)) = natElem k := by
  rw [← push_natElem_vecElem, searchMap_rec, head_push, tail_push,
    push_natElem_vecElem, lamDef_coe_val hf (k ::ᵥ v), h0, zeroMap_natElem_zero,
    Exercise326.cond_true]

theorem searchMap_step_next {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n) (k : ℕ)
    (hne : f (k ::ᵥ v) ≠ 0) :
    (searchMap φf).toElementMap (vecElem (k ::ᵥ v)) =
      (searchMap φf).toElementMap (vecElem ((k + 1) ::ᵥ v)) := by
  obtain ⟨m, hm⟩ : ∃ m, f (k ::ᵥ v) = m + 1 := ⟨f (k ::ᵥ v) - 1, by omega⟩
  rw [← push_natElem_vecElem, searchMap_rec, head_push, tail_push,
    push_natElem_vecElem, lamDef_coe_val hf (k ::ᵥ v), hm, zeroMap_natElem_succ,
    Exercise326.cond_false, succMap_natElem, push_natElem_vecElem]

theorem searchMap_climb {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n) (m : ℕ)
    (hm0 : f (m ::ᵥ v) = 0) (hmin : ∀ i, i < m → f (i ::ᵥ v) ≠ 0) :
    ∀ d j, j + d = m → (searchMap φf).toElementMap (vecElem (j ::ᵥ v)) = natElem m := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have hjm : j = m := by omega
    rw [hjm]
    exact searchMap_step_found φf hf v m hm0
  | succ d ih =>
    intro j hj
    have hjm : j < m := by omega
    rw [searchMap_step_next φf hf v j (hmin j hjm)]
    exact ih (j + 1) (by omega)

theorem iterVal_zero (z : 𝒩.Element) :
    (toApproxMap ((findOp φf).iterElem 0)).toElementMap z = N.bot := by
  rw [findOp_iterElem_zero, toApproxMap_bot]

theorem iterVal_bot {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n)
    (hdiv : ∀ k, f (k ::ᵥ v) ≠ 0) :
    ∀ m k, (toApproxMap ((findOp φf).iterElem m)).toElementMap (vecElem (k ::ᵥ v)) = N.bot := by
  intro m
  induction m with
  | zero => intro k; exact iterVal_zero φf (vecElem (k ::ᵥ v))
  | succ m ih =>
    intro k
    have hne := hdiv k
    obtain ⟨j, hj⟩ : ∃ j, f (k ::ᵥ v) = j + 1 := ⟨f (k ::ᵥ v) - 1, by omega⟩
    rw [← push_natElem_vecElem, iterVal_succ, head_push, tail_push,
      push_natElem_vecElem, lamDef_coe_val hf (k ::ᵥ v), hj, zeroMap_natElem_succ,
      Exercise326.cond_false, succMap_natElem, push_natElem_vecElem]
    exact ih (k + 1)

theorem searchMap_diverge {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n)
    (hdiv : ∀ k, f (k ::ᵥ v) ≠ 0) (k : ℕ) :
    (searchMap φf).toElementMap (vecElem (k ::ᵥ v)) = N.bot := by
  refine le_antisymm ?_ (N.bot_le _)
  rw [searchMap, ← evalAt_apply, fixElement_eq_iSupDirected, toElementMap_iSupDirected]
  apply NeighborhoodSystem.iSupDirected_le
  intro m
  rw [evalAt_apply]
  exact le_of_eq (iterVal_bot φf hf v hdiv m k)

end Rfind

section Prec
variable (φf φg : ApproximableMap 𝒩 N)

def precBody : ApproximableMap (prod (funSpace 𝒩 N) 𝒩) N :=
  (cond N).comp
    (paired (zeroMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
      (paired (φf.comp ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
        (φg.comp
          ((push N).comp
            (paired (predMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
              ((push N).comp
                (paired
                  ((evalMap 𝒩 N).comp
                    (paired (proj₀ (funSpace 𝒩 N) 𝒩)
                      ((push N).comp
                        (paired (predMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
                          ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩))))))
                  ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))))))))

def recOp : ApproximableMap (funSpace 𝒩 N) (funSpace 𝒩 N) := curry (precBody φf φg)

def recMap : ApproximableMap 𝒩 N := toApproxMap (recOp φf φg).fixElement

theorem precBody_apply (k : (funSpace 𝒩 N).Element) (z : 𝒩.Element) :
    (precBody φf φg).toElementMap (pair k z) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap ((head N).toElementMap z))
          (pair (φf.toElementMap ((tail N).toElementMap z))
            (φg.toElementMap
              ((push N).toElementMap
                (pair (predMap.toElementMap ((head N).toElementMap z))
                  ((push N).toElementMap
                    (pair ((toApproxMap k).toElementMap
                            ((push N).toElementMap
                              (pair (predMap.toElementMap ((head N).toElementMap z))
                                ((tail N).toElementMap z))))
                      ((tail N).toElementMap z)))))))) := by
  rw [precBody, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

theorem recMap_rec (z : 𝒩.Element) :
    (recMap φf φg).toElementMap z =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap ((head N).toElementMap z))
          (pair (φf.toElementMap ((tail N).toElementMap z))
            (φg.toElementMap
              ((push N).toElementMap
                (pair (predMap.toElementMap ((head N).toElementMap z))
                  ((push N).toElementMap
                    (pair ((recMap φf φg).toElementMap
                            ((push N).toElementMap
                              (pair (predMap.toElementMap ((head N).toElementMap z))
                                ((tail N).toElementMap z))))
                      ((tail N).toElementMap z)))))))) := by
  have hfix : (recOp φf φg).toElementMap (recOp φf φg).fixElement = (recOp φf φg).fixElement :=
    toElementMap_fixElement (recOp φf φg)
  have hval := toElementMap_curry_apply (precBody φf φg) (recOp φf φg).fixElement z
  rw [← recOp, hfix] at hval
  rw [recMap, hval, precBody_apply]

theorem recMap_eval {n : ℕ} (f₀ : List.Vector ℕ n → ℕ) (g₀ : List.Vector ℕ (n + 2) → ℕ)
    (hf : LamDef φf (f₀ : List.Vector ℕ n →. ℕ)) (hg : LamDef φg (g₀ : List.Vector ℕ (n + 2) →. ℕ))
    (u : List.Vector ℕ n) (d : ℕ) :
    (recMap φf φg).toElementMap (vecElem (d ::ᵥ u))
      = natElem (Nat.rec (motive := fun _ => ℕ) (f₀ u)
          (fun y IH => g₀ (y ::ᵥ IH ::ᵥ u)) d) := by
  induction d with
  | zero =>
    rw [← push_natElem_vecElem, recMap_rec, head_push, tail_push,
      zeroMap_natElem_zero, Exercise326.cond_true]
    exact lamDef_coe_val hf u
  | succ d ih =>
    rw [← push_natElem_vecElem, recMap_rec, head_push, tail_push,
      zeroMap_natElem_succ, Exercise326.cond_false, predMap_natElem_succ, push_natElem_vecElem, ih,
      push_natElem_vecElem, push_natElem_vecElem]
    exact lamDef_coe_val hg _

end Prec

end DomainTheory.NeighbourhoodSystems.PartrecLam
