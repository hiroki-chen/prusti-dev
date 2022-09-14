use std::collections::BTreeMap;

use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        footprint::FootprintInterface,
        lowerer::Lowerer,
        places::PlacesInterface,
        pointers::PointersInterface,
        predicates::{PredicatesMemoryBlockInterface, PredicatesOwnedInterface},
        references::ReferencesInterface,
        snapshots::{
            IntoAssertion, IntoPureSnapshot, IntoSnapshot, IntoSnapshotLowerer,
            SnapshotBytesInterface, SnapshotValidityInterface, SnapshotValuesInterface,
        },
        type_layouts::TypeLayoutsInterface,
        utils::place_domain_encoder::PlaceExpressionDomainEncoder,
    },
};
use prusti_common::config;
use vir_crate::{
    common::{
        expression::{GuardedExpressionIterator, QuantifierHelpers},
        position::Positioned,
    },
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

pub(super) struct AssertionEncoder<'a> {
    /// A map from field names to arguments that are being assigned to these
    /// fields.
    field_arguments: BTreeMap<String, vir_low::Expression>,
    heap: &'a vir_low::VariableDecl,
}

impl<'a> AssertionEncoder<'a> {
    pub(super) fn new(
        decl: &vir_mid::type_decl::Struct,
        operand_values: Vec<vir_low::Expression>,
        heap: &'a vir_low::VariableDecl,
    ) -> Self {
        let mut field_arguments = BTreeMap::default();
        assert_eq!(decl.fields.len(), operand_values.len());
        for (field, operand) in decl.fields.iter().zip(operand_values.into_iter()) {
            assert!(field_arguments
                .insert(field.name.clone(), operand)
                .is_none());
        }
        Self {
            field_arguments,
            heap,
        }
    }

    // FIXME: Code duplication.
    fn pointer_deref_into_address<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if let Some(deref_place) = place.get_last_dereferenced_pointer() {
            let base_snapshot = self.expression_to_snapshot(lowerer, deref_place, true)?;
            let ty = deref_place.get_type();
            lowerer.pointer_address(ty, base_snapshot, place.position())
            // match deref_place {
            //     vir_mid::Expression::Deref(deref) => {
            //         let base_snapshot = self.expression_to_snapshot(lowerer, &deref.base, true)?;
            //         let ty = deref.base.get_type();
            //         assert!(ty.is_pointer());
            //         lowerer.pointer_address(ty, base_snapshot, place.position())
            //     }
            //     _ => unreachable!(),
            // }
        } else {
            unreachable!()
        }
        // PlaceExpressionDomainEncoder::encode_expression(self, place, lowerer)
    }

    pub(super) fn address_in_heap<'p, 'v, 'tcx>(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        pointer_place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let pointer = self.expression_to_snapshot(lowerer, pointer_place, true)?;
        let address =
            lowerer.pointer_address(pointer_place.get_type(), pointer, pointer_place.position())?;
        let in_heap = vir_low::Expression::container_op_no_pos(
            vir_low::ContainerOpKind::MapContains,
            self.heap.ty.clone(),
            vec![self.heap.clone().into(), address],
        );
        Ok(in_heap)
    }
}

// impl<'a> PlaceExpressionDomainEncoder for AssertionEncoder<'a> {
//     fn domain_name(&mut self, lowerer: &mut Lowerer) -> &str {
//         lowerer.address_domain()
//     }

//     fn encode_local(
//         &mut self,
//         local: &vir_mid::expression::Local,
//         lowerer: &mut Lowerer,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         lowerer.root_address(local, &None)
//     }

//     fn encode_deref(
//         &mut self,
//         deref: &vir_mid::expression::Deref,
//         lowerer: &mut Lowerer,
//         _arg: vir_low::Expression,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         let base_snapshot = self.expression_to_snapshot(lowerer, &deref.base, true)?;
//         let ty = deref.base.get_type();
//         let result = if ty.is_reference() {
//             lowerer.reference_address(ty, base_snapshot, deref.position)?
//         } else {
//             lowerer.pointer_address(ty, base_snapshot, deref.position)?
//         };
//         Ok(result)
//     }

//     fn encode_labelled_old(
//         &mut self,
//         _expression: &vir_mid::expression::LabelledOld,
//         _lowerer: &mut Lowerer,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         todo!()
//     }

//     fn encode_array_index_axioms(
//         &mut self,
//         _base_type: &vir_mid::Type,
//         _lowerer: &mut Lowerer,
//     ) -> SpannedEncodingResult<()> {
//         todo!()
//     }
// }

impl<'a, 'p, 'v: 'p, 'tcx: 'v> IntoSnapshotLowerer<'p, 'v, 'tcx> for AssertionEncoder<'a> {
    fn variable_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        Ok(vir_low::VariableDecl {
            name: variable.name.clone(),
            ty: self.type_to_snapshot(lowerer, &variable.ty)?,
        })
    }

    fn labelled_old_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        old: &vir_mid::LabelledOld,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn func_app_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        app: &vir_mid::FuncApp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn acc_predicate_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        acc_predicate: &vir_mid::AccPredicate,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(expect_math_bool);
        let expression = match &*acc_predicate.predicate {
            vir_mid::Predicate::OwnedNonAliased(predicate) => {
                let ty = predicate.place.get_type();
                let place = lowerer.encode_expression_as_place(&predicate.place)?;
                // eprintln!("predicate: {}", predicate);
                let root_address = self.pointer_deref_into_address(lowerer, &predicate.place)?;
                // eprintln!("root_address2: {}", root_address);
                // let deref = predicate.place.clone().unwrap_deref();
                // let base_snapshot =
                //     self.expression_to_snapshot(lowerer, &deref.base, expect_math_bool)?;
                // let snapshot = lowerer.pointer_target_snapshot_in_heap(
                //     deref.base.get_type(),
                //     self.heap.clone(),
                //     base_snapshot,
                //     deref.position,
                // )?;
                let snapshot =
                    self.expression_to_snapshot(lowerer, &predicate.place, expect_math_bool)?;
                let acc = lowerer.owned_non_aliased(
                    CallContext::Procedure,
                    ty,
                    ty,
                    place,
                    root_address,
                    snapshot,
                    None,
                )?;
                acc
            }
            vir_mid::Predicate::MemoryBlockHeap(predicate) => {
                let place = lowerer.encode_expression_as_place(&predicate.address)?;
                let root_address = self.pointer_deref_into_address(lowerer, &predicate.address)?;
                use vir_low::macros::*;
                let compute_address = ty!(Address);
                let address = expr! {
                    ComputeAddress::compute_address([place], [root_address])
                };
                let size =
                    self.expression_to_snapshot(lowerer, &predicate.size, expect_math_bool)?;
                lowerer.encode_memory_block_stack_acc(address, size, acc_predicate.position)?
            }
            vir_mid::Predicate::MemoryBlockHeapDrop(predicate) => {
                let place = self.pointer_deref_into_address(lowerer, &predicate.address)?;
                let size =
                    self.expression_to_snapshot(lowerer, &predicate.size, expect_math_bool)?;
                lowerer.encode_memory_block_heap_drop_acc(place, size, acc_predicate.position)?
            }
            _ => unimplemented!("{acc_predicate}"),
        };
        Ok(expression)
    }

    fn field_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        field: &vir_mid::Field,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        match &*field.base {
            vir_mid::Expression::Local(local) => {
                assert!(local.variable.is_self_variable());
                Ok(self.field_arguments[&field.field.name].clone())
            }
            _ => {
                // FIXME: Code duplication because Rust does not have syntax for calling
                // overriden methods.
                let base_snapshot =
                    self.expression_to_snapshot(lowerer, &field.base, expect_math_bool)?;
                let result = if field.field.is_discriminant() {
                    let ty = field.base.get_type();
                    // FIXME: Create a method for obtainging the discriminant type.
                    let type_decl = lowerer.encoder.get_type_decl_mid(ty)?;
                    let enum_decl = type_decl.unwrap_enum();
                    let discriminant_call =
                        lowerer.obtain_enum_discriminant(base_snapshot, ty, field.position)?;
                    lowerer.construct_constant_snapshot(
                        &enum_decl.discriminant_type,
                        discriminant_call,
                        field.position,
                    )?
                } else {
                    lowerer.obtain_struct_field_snapshot(
                        field.base.get_type(),
                        &field.field,
                        base_snapshot,
                        field.position,
                    )?
                };
                self.ensure_bool_expression(lowerer, field.get_type(), result, expect_math_bool)
            }
        }
    }

    fn deref_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        deref: &vir_mid::Deref,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        eprintln!("deref: {}", deref);
        eprintln!("  deref: {:?}", deref);
        let base_snapshot = self.expression_to_snapshot(lowerer, &deref.base, expect_math_bool)?;
        eprintln!("  reference_base type: {}", deref.base.get_type());
        let ty = deref.base.get_type();
        let result = if ty.is_reference() {
            lowerer.reference_target_current_snapshot(ty, base_snapshot, Default::default())?
        } else {
            lowerer.pointer_target_snapshot_in_heap(
                deref.base.get_type(),
                self.heap.clone(),
                base_snapshot,
                deref.position,
            )?
        };
        self.ensure_bool_expression(lowerer, deref.get_type(), result, expect_math_bool)
    }
}
