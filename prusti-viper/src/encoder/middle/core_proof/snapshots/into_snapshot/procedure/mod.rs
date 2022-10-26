//! Code for encoding expressions into snapshots in non-pure contexts such as
//! procedure bodies. Most important difference from `pure` is that this
//! encoding uses SSA.

use super::common::IntoSnapshotLowerer;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        lowerer::{FunctionsLowererInterface, Lowerer},
        places::PlacesInterface,
        pointers::PointersInterface,
        predicates::{PredicatesMemoryBlockInterface, PredicatesOwnedInterface},
        references::ReferencesInterface,
        snapshots::SnapshotVariablesInterface,
    },
};
use vir_crate::{
    common::{
        expression::BinaryOperationHelpers, identifier::WithIdentifier, position::Positioned,
    },
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

mod traits;

pub(in super::super::super) use self::traits::{
    IntoProcedureAssertion, IntoProcedureBoolExpression, IntoProcedureFinalSnapshot,
    IntoProcedureSnapshot,
};

#[derive(Default)]
struct ProcedureSnapshot {
    old_label: Option<String>,
    deref_to_final: bool,
    is_assertion: bool,
    in_heap_assertions: Vec<vir_low::Expression>,
}

impl<'p, 'v: 'p, 'tcx: 'v> IntoSnapshotLowerer<'p, 'v, 'tcx> for ProcedureSnapshot {
    fn variable_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        if let Some(label) = &self.old_label {
            lowerer.snapshot_variable_version_at_label(variable, label)
        } else {
            lowerer.current_snapshot_variable_version(variable)
        }
    }

    fn func_app_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        app: &vir_mid::FuncApp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let arguments =
            self.expression_vec_to_snapshot(lowerer, &app.arguments, expect_math_bool)?;
        let return_type = self.type_to_snapshot(lowerer, &app.return_type)?;
        let func_app = lowerer.call_pure_function_in_procedure_context(
            app.get_identifier(),
            arguments,
            return_type,
            app.position,
        )?;
        let result = vir_low::Expression::FuncApp(func_app);
        self.ensure_bool_expression(lowerer, &app.return_type, result, expect_math_bool)
    }

    fn labelled_old_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        old: &vir_mid::LabelledOld,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let parent_old_label = std::mem::replace(&mut self.old_label, Some(old.label.clone()));
        let result = self.expression_to_snapshot(lowerer, &old.base, expect_math_bool);
        self.old_label = parent_old_label;
        result
    }

    fn deref_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        deref: &vir_mid::Deref,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let result = if self.deref_to_final {
            self.deref_to_final = false;
            let base_snapshot =
                self.expression_to_snapshot(lowerer, &deref.base, expect_math_bool)?;
            self.deref_to_final = true;
            lowerer.reference_target_final_snapshot(
                deref.base.get_type(),
                base_snapshot,
                deref.position,
            )?
        } else {
            let base_snapshot =
                self.expression_to_snapshot(lowerer, &deref.base, expect_math_bool)?;
            if deref.base.get_type().is_reference() {
                lowerer.reference_target_current_snapshot(
                    deref.base.get_type(),
                    base_snapshot,
                    deref.position,
                )?
            } else {
                lowerer.pointer_target_snapshot(
                    deref.base.get_type(),
                    &self.old_label,
                    base_snapshot,
                    deref.position,
                )?
            }
        };
        self.ensure_bool_expression(lowerer, deref.get_type(), result, expect_math_bool)
    }

    fn acc_predicate_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        acc_predicate: &vir_mid::AccPredicate,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(self.is_assertion);
        fn in_heap<'p, 'v, 'tcx>(
            old_label: &Option<String>,
            place: &vir_mid::Expression,
            lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        ) -> SpannedEncodingResult<vir_low::Expression> {
            let in_heap = if let Some(pointer_place) = place.get_last_dereferenced_pointer() {
                let pointer = pointer_place.to_procedure_snapshot(lowerer)?;
                let address =
                    lowerer.pointer_address(pointer_place.get_type(), pointer, place.position())?;
                let heap = lowerer.heap_variable_version_at_label(old_label)?;
                vir_low::Expression::container_op_no_pos(
                    vir_low::ContainerOpKind::MapContains,
                    heap.ty.clone(),
                    vec![heap.into(), address],
                )
            } else {
                unimplemented!("TODO: Proper error message: {:?}", place);
            };
            Ok(in_heap)
        }
        let expression = match &*acc_predicate.predicate {
            vir_mid::Predicate::OwnedNonAliased(predicate) => {
                let ty = predicate.place.get_type();
                let place = lowerer.encode_expression_as_place(&predicate.place)?;
                let root_address = lowerer.extract_root_address(&predicate.place)?;
                let snapshot = predicate.place.to_procedure_snapshot(lowerer)?; // FIXME: This is probably wrong. It should take into account the current old.
                let in_heap = in_heap(&self.old_label, &predicate.place, lowerer)?;
                self.in_heap_assertions.push(in_heap);
                // let acc =
                lowerer.owned_aliased(
                    CallContext::Procedure,
                    ty,
                    ty,
                    place,
                    root_address,
                    snapshot,
                    None,
                )?
                // ;
                // vir_low::Expression::and(in_heap, acc)
            }
            vir_mid::Predicate::MemoryBlockHeap(predicate) => {
                let place = lowerer.encode_expression_as_place_address(&predicate.address)?;
                let size = predicate.size.to_procedure_snapshot(lowerer)?;
                let in_heap = in_heap(&self.old_label, &predicate.address, lowerer)?;
                self.in_heap_assertions.push(in_heap);
                // let acc =
                lowerer.encode_memory_block_stack_acc(place, size, acc_predicate.position)?
                //;
                // vir_low::Expression::and(in_heap, acc)
            }
            vir_mid::Predicate::MemoryBlockHeapDrop(predicate) => {
                let place = lowerer.encode_expression_as_place_address(&predicate.address)?;
                let size = predicate.size.to_procedure_snapshot(lowerer)?;
                let in_heap = in_heap(&self.old_label, &predicate.address, lowerer)?;
                self.in_heap_assertions.push(in_heap);
                // let acc =
                lowerer.encode_memory_block_heap_drop_acc(place, size, acc_predicate.position)?
                // ;
                // vir_low::Expression::and(in_heap, acc)
            }
            _ => unimplemented!("{acc_predicate}"),
        };
        Ok(expression)
    }
}
