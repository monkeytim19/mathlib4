/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.GroupTheory.GroupAction.Defs

#align_import group_theory.group_action.opposite from "leanprover-community/mathlib"@"4330aae21f538b862f8aead371cfb6ee556398f1"

/-!
# Scalar actions on and by `Mᵐᵒᵖ`

This file defines the actions on the opposite type `SMul R Mᵐᵒᵖ`, and actions by the opposite
type, `SMul Rᵐᵒᵖ M`.

Note that `MulOpposite.smul` is provided in an earlier file as it is needed to
provide the `AddMonoid.nsmul` and `AddCommGroup.zsmul` fields.

## Notation

With `open scoped RightActions`, this provides:

* `r •> m` as an alias for `r • m`
* `m <• r` as an alias for `MulOpposite.op r • m`
* `v +ᵥ> p` as an alias for `v +ᵥ p`
* `p <+ᵥ v` as an alias for `AddOpposite.op v +ᵥ p`
-/


variable {R M N α : Type*}

/-! ### Actions _on_ the opposite type

Actions on the opposite type just act on the underlying type.
-/


namespace MulOpposite

instance instDistribMulAction [Monoid M] [AddMonoid α] [DistribMulAction M α] :
    DistribMulAction M αᵐᵒᵖ where
  smul_add _ _ _ := unop_injective <| smul_add _ _ _
  smul_zero _ := unop_injective <| smul_zero _

instance instMulDistribMulAction [Monoid M] [Monoid α] [MulDistribMulAction M α] :
    MulDistribMulAction M αᵐᵒᵖ where
  smul_mul _ _ _ := unop_injective <| smul_mul' _ _ _
  smul_one _ := unop_injective <| smul_one _

@[to_additive]
instance instIsScalarTower [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower M N αᵐᵒᵖ where
  smul_assoc _ _ _ := unop_injective <| smul_assoc _ _ _

@[to_additive]
instance instSMulCommClass [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M N αᵐᵒᵖ where
  smul_comm _ _ _ := unop_injective <| smul_comm _ _ _

@[to_additive]
instance instIsCentralScalar [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] :
    IsCentralScalar M αᵐᵒᵖ where
  op_smul_eq_smul _ _ := unop_injective <| op_smul_eq_smul _ _

theorem op_smul_eq_op_smul_op [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] (r : M) (a : α) :
    op (r • a) = op r • op a := (op_smul_eq_smul r (op a)).symm
#align mul_opposite.op_smul_eq_op_smul_op MulOpposite.op_smul_eq_op_smul_op

theorem unop_smul_eq_unop_smul_unop [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] (r : Mᵐᵒᵖ)
    (a : αᵐᵒᵖ) : unop (r • a) = unop r • unop a := (unop_smul_eq_smul r (unop a)).symm
#align mul_opposite.unop_smul_eq_unop_smul_unop MulOpposite.unop_smul_eq_unop_smul_unop

end MulOpposite

/-! ### Actions _by_ the opposite type (right actions)

In `Mul.toSMul` in another file, we define the left action `a₁ • a₂ = a₁ * a₂`. For the
multiplicative opposite, we define `MulOpposite.op a₁ • a₂ = a₂ * a₁`, with the multiplication
reversed.
-/

open MulOpposite

/-- `Monoid.toOppositeMulAction` is faithful on nontrivial cancellative monoids with zero. -/
instance CancelMonoidWithZero.toFaithfulSMul_opposite [CancelMonoidWithZero α]
    [Nontrivial α] : FaithfulSMul αᵐᵒᵖ α :=
  ⟨fun h => unop_injective <| mul_left_cancel₀ one_ne_zero (h 1)⟩
#align cancel_monoid_with_zero.to_has_faithful_opposite_scalar CancelMonoidWithZero.toFaithfulSMul_opposite
