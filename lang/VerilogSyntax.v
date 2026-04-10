(* COPYRIGHT LICENSE: CC-BY 4.0 from https://zenodo.org/records/16923443 *)
(* CONTRIBUTOR CREDITS: Choi, Joonwon; Kim, Jaewoo; Kang, Jeehoon *)
(* Modified for use in Quartz; modifications dual-licensed MIT + CC-BY-4.0 *)

Require Import Coq.ZArith.BinInt Coq.Lists.List.
Local Open Scope Z.

Declare Custom Entry verilog_top.
Declare Custom Entry verilog_module.
Declare Custom Entry verilog_gen.
Declare Custom Entry verilog_paramports.
Declare Custom Entry verilog_ports.
Declare Custom Entry verilog_stmt.

Declare Custom Entry verilog_assign.
Declare Custom Entry verilog_netdeclassign.
Declare Custom Entry verilog_vardeclassign.
Declare Custom Entry verilog_paramassign.
Declare Custom Entry verilog_blockingassign.

Declare Custom Entry verilog_portconn.
Declare Custom Entry verilog_portconnid.
Declare Custom Entry verilog_packeddim.
Declare Custom Entry verilog_pexpr.
Declare Custom Entry verilog_expr.
Declare Custom Entry verilog_lit.

Notation "verilog_top:( t ')'" := t (t custom verilog_top).

Section VModuleDecl.
  Context {VId: Set}.

  (*! Expressions -- *)

  (* decimal_number ::= *)
  (* (v)   unsigned_number *)
  (* (v) | [ size ] decimal_base unsigned_number *)
  (* | [ size ] decimal_base x_digit { _ } *)
  (* | [ size ] decimal_base z_digit { _ } *)
  Inductive VDecimalNumber :=
  | VDecimalNumberNB (v: Z)
  | VDecimalNumberB (sz: option Z) (v: Z).

  (* integral_number ::= *)
  (* (v)   decimal_number *)
  (* (v) | octal_number *)
  (* (v) | binary_number *)
  (* (v) | hex_number *)
  (* (v) binary_number ::= [ size ] binary_base binary_value *)
  (* (v) octal_number ::= [ size ] octal_base octal_value *)
  (* (v) hex_number ::= [ size ] hex_base hex_value *)
  Inductive VIntegralNumber :=
  | VIntegralBinary (sz: option Z) (v: Z)
  | VIntegralOctal (sz: option Z) (v: Z)
  | VIntegralHex (sz: option Z) (v: Z)
  | VIntegralDecimal (d: VDecimalNumber).
  Coercion VIntegralDecimal: VDecimalNumber >-> VIntegralNumber.

  (* (v) number ::= integral_number | real_number *)
  Inductive VNumber :=
  | VNumberIntegral (i: VIntegralNumber).
  Coercion VNumberIntegral: VIntegralNumber >-> VNumber.

  (* unbased_unsized_literal ::= '0 | '1 | 'z_or_x *)
  Inductive VUnbasedUnsizedLiteral := VZeros | VOnes.

  (* primary_literal ::= *)
  (* (v)   number *)
  (* | time_literal *)
  (* (v) | unbased_unsized_literal *)
  (* | string_literal *)
  Inductive VPriLiteral :=
  | VPriLiteralNumber (n: VNumber)
  | VPriLiteralUU (uu: VUnbasedUnsizedLiteral).
  Coercion VPriLiteralNumber: VNumber >-> VPriLiteral.
  Coercion VPriLiteralUU: VUnbasedUnsizedLiteral >-> VPriLiteral.

  (* (v) unary_operator ::= *)
  (* + | - | ! | ~ | & | ~& | | | ~| | ^ | ~^ | ^~ *)
  Inductive VUniOp :=
  | VUniPlus | VUniMinus | VUniNot | VUniNeg
  | VUniAnd | VUniNand | VUniOr | VUniNor | VUniXor | VUniXnor.

  (* (v) binary_operator ::= *)
  (*   + | - | * | / | % | == | != | === | !== | =?= | !?= | && | || | ** *)
  (* | < |<= | > | >=| & | |  | ^  | ^~  | ~^  | >>  | <<  | >>>| <<< *)
  Inductive VBinOp :=
  | VBinAdd | VBinSub | VBinMul | VBinDiv | VBinRem | VBinEq | VBinNEq | VBinFEq | VBinFNEq
  | VBinWEq | VBinWNEq | VBinLAnd | VBinLOr | VBinPow
  | VBinLt | VBinLe | VBinGt | VBinGe | VBinBAnd | VBinBOr | VBinBXor | VBinBXnor
  | VBinShr | VBinShl | VBinSar | VBinSal.

  (* inc_or_dec_expression ::= *)
  (* (v)   inc_or_dec_operator { attribute_instance } variable_lvalue *)
  (* (v) | variable_lvalue { attribute_instance } inc_or_dec_operator *)
  Inductive VIncOrDecExpr :=
  | VIncExpr (vid: VId)
  | VDecExpr (vid: VId).

  Inductive VSystemTf :=
  | VSystemTfSigned
  | VSystemTfUnsigned.

  (** NOTE:
   * 1) `primary` is merged into `expression`, since it has `expression` recursively.
   * 2) L-values use VExpr (partially).
   * 3) Constant expressions use VExpr partially= as well.
   *)
  (* primary ::= *)
  (* (v)   primary_literal *)
  (* (v) | [ implicit_class_handle . | class_scope | package_scope ] hierarchical_identifier select *)
  (* (v) | empty_queue *)
  (* (v) | concatenation *)
  (* (v) | multiple_concatenation *)
  (* (v) | function_subroutine_call *)
  (* | ( mintypmax_expression ) *)
  (* (v) | cast *)
  (* | streaming_expression *)
  (* | sequenverilog_method_call *)
  (* | $ *)
  (* | null *)
  (* expression ::= *)
  (* (v)   primary *)
  (* (v) | unary_operator { attribute_instance } primary *)
  (* (v) | inc_or_dec_expression *)
  (* (?) | ( operator_assignment ) *) (** No idea why it belongs to expressions *)
  (* (v) | expression binary_operator { attribute_instance } expression *)
  (* (v) | conditional_expression *)
  (* (v) | inside_expression *)
  (* | tagged_union_expression *)
  Inductive VExpr: Set :=
  | VExprPriLiteral (pl: VPriLiteral)

  (* hierarchical_identifier ::= [ $root . ] { identifier { [ constant_expression ] } . } identifier *)
  (* select ::= { [ expression ] } [ [ part_select_range ] ] *)
  (* part_select_range ::= constant_range | indexed_range *)
  (* indexed_range ::= *)
  (*   expression +: constant_expression *)
  (* | expression -: constant_expression *)
  | VExprId (n: VId)
  | VExprHier (pe ce: VExpr)
  | VExprPriSelect (te se: VExpr)
  | VExprPriSelectConstRange (se lr rr: VExpr)
  | VExprPriSelectIdxRangeAdd (se lr rr: VExpr)
  | VExprPriSelectIdxRangeSub (se lr rr: VExpr)

  (** NOTE: maybe fine to regard (VExprPriConcat nil) as an empty queue *)
  (* concatenation ::= *)
  (* (v)   { expression { , expression } } *)
  (* | { struct_member_label : expression { , struct_member_label : expression } } *)
  (* | { array_member_label : expression { , array_member_label : expression } } *)
  | VExprPriConcat (es: list VExpr)

  (* multiple_concatenation ::= { expression concatenation } *)
  | VExprPriMultConcat (ne: VExpr) (ces: list VExpr)

  (* function_subroutine_call ::= subroutine_call *)
  (* subroutine_call ::= tf_call | (v) system_tf_call | method_call | randomize_call *)
  (* system_tf_call ::= system_tf_identifier [ ( list_of_arguments ) ] *)
  | VExprTfCall (tfid: VId) (aes: list VExpr)
  | VExprSystemTfCall (tf: VSystemTf) (aes: list VExpr)

  (* cast ::= *)
  (* (v)   casting_type ' ( expression ) *)
  (* | casting_type ' concatenation *)
  (* | casting_type ' multiple_concatentation *)
  | VExprCast (sze: VExpr) (e: VExpr)

  | VExprUniOp (op: VUniOp) (e: VExpr)
  | VExprIncOrDec (iod: VIncOrDecExpr)
  | VExprBinOp (op: VBinOp) (le re: VExpr)
  (** NOTE: need to implement patterns; see [VCondPredicate] *)
  (* conditional_expression ::= cond_predicate ? { attribute_instance } expression : expression *)
  | VExprCond (ce te fe: VExpr)
  (* inside_expression ::= expression inside { open_range_list } *)
  (* open_range_list ::= open_value_range { , open_value_range } *)
  (* open_value_range ::= value_range *)
  | VExprInside (ie: VExpr) (res: list VExpr).
  Coercion VExprIncOrDec: VIncOrDecExpr >-> VExpr.

  (** NOTE: cannot use coercion from VPriLiteral to VExpr,
   * since VExpr is parameterized by {VId} (not uniformly inherited).
   * In order to solve this problem, we declare a custom entry for VPriLiteral and
   * define the following notation:
   * Notation "p" := (VExprPriLiteral p)
   *   (in custom verilog_expr at level 94, p custom verilog_lit at level 94).
   *)
  (* Coercion VExprPriLiteral: VPriLiteral >-> VExpr. *)
  (** NOTE: cannot use this coercion as well, dropped when closing the section *)
  (* Coercion VExprId: VId >-> VExpr. *)

  Definition VLValue := VExpr.

  (* net_lvalue ::= *)
  (*   ps_or_hierarchical_net_identifier constant_select *)
  (* | { net_lvalue { , net_lvalue } } *)
  Definition VNetLValue := VLValue.
  (* variable_lvalue ::= *)
  (*   [ implicit_class_handle . | package_scope ] hierarchical_variable_identifier select *)
  (* | { variable_lvalue { , variable_lvalue } } *)
  Definition VVarLValue := VLValue.

  (* constant_primary ::= *)
  (* (v)   primary_literal *)
  (* | ps_parameter_identifier *)
  (* | ps_specparam_identifier *)
  (* | genvar_identifier *)
  (* | [ package_scope | class_scope ] enum_identifier *)
  (* | constant_concatentation *)
  (* | constant_multiple_concatenation *)
  (* | constant_function_call *)
  (* | ( constant_mintypmax_expression ) *)
  (* | constant_cast *)
  (* Inductive VConstPrimary := *)
  (* | VConstPrimaryLiteral (pl: VPriLiteral). *)
  (* Coercion VConstPrimaryLiteral: VPriLiteral >-> VConstPrimary. *)

  (** NOTE: it looks redundant to define `constant_mintypmax_expression` and
   * `constant_expression` separately. `expression` already contains both,
   * thus we use VExpr here. *)
  (* constant_param_expression ::= constant_mintypmax_expression | data_type | $ *)
  Inductive VConstParamExpr :=
  | VConstParamExprMinTypMax (ce: VExpr).
  Coercion VConstParamExprMinTypMax: VExpr >-> VConstParamExpr.

  Inductive VEdgeId := VPosedge | VNegedge.

  (* event_expression ::= *)
  (*   [ edge_identifier ] expression [ iff expression ] *)
  (* | sequenverilog_instance [ iff expression ] *)
  (* | event_expression or event_expression *)
  (* | event_expression , event_expression *)
  Inductive VEventExpr :=
  | VEventExprExpr (eid: option VEdgeId) (e: VExpr)
  | VEventExprOr (le re: VEventExpr).

  (* event_control ::= *)
  (*   @ hierarchical_event_identifier *)
  (* (v) | @ ( event_expression ) *)
  (* (v) | @* *)
  (* (v) | @ \(\*\) *)
  (* | @ sequenverilog_instance *)
  Inductive VEventControl :=
  | VEventControlExpr (ee: VEventExpr)
  | VEventControlAny.
  Coercion VEventControlExpr: VEventExpr >-> VEventControl.

  (* property_expr ::= *)
  (* (v) | sequenverilog_expr *)
  (* (v) | ( property_expr ) *)
  (* (v) | not property_expr *)
  (* (v) | property_expr or property_expr *)
  (* (v) | property_expr and property_expr *)
  (* (v) | sequenverilog_expr |-> property_expr *)
  (* (v) | sequenverilog_expr |=> property_expr *)
  (* (v) | if ( expression_or_dist ) property_expr [ else property_expr ] *)
  (* | property_instance *)
  (* (v) | clocking_event property_expr *)
  (* sequenverilog_expr ::= *)
  (* | cycle_delay_range sequenverilog_expr { cycle_delay_range sequenverilog_expr } *)
  (* | sequenverilog_expr cycle_delay_range sequenverilog_expr { cycle_delay_range sequenverilog_expr } *)
  (* (v) | expression_or_dist [ boolean_abbrev ] *)
  (* | ( expression_or_dist {, sequenverilog_match_item } ) [ boolean_abbrev ] *)
  (* | sequenverilog_instance [ sequenverilog_abbrev ] *)
  (* | ( sequenverilog_expr {, sequenverilog_match_item } ) [ sequenverilog_abbrev ] *)
  (* (v) | sequenverilog_expr and sequenverilog_expr *)
  (* (v) | sequenverilog_expr intersect sequenverilog_expr *)
  (* (v) | sequenverilog_expr or sequenverilog_expr *)
  (* | first_match ( sequenverilog_expr {, sequenverilog_match_item} ) | expression_or_dist throughout sequenverilog_expr *)
  (* (v) | sequenverilog_expr within sequenverilog_expr *)
  (* (v) | clocking_event sequenverilog_expr *)
  (** Decided to merge property_expr and sequenverilog_expr; let's revisit if any issues occur. *)
  Inductive VPExpr :=
  (** For property_expr *)
  | VPExprNot (se: VPExpr)
  | VPExprOr (lse rse: VPExpr)
  | VPExprAnd (lse rse: VPExpr)
  | VPExprImp (lse rse: VPExpr)
  | VPExprImpN (lse rse: VPExpr)
  | VPExprIfElse (ce: VExpr) (tse: VPExpr) (fse: option VPExpr)
  | VPExprClk (ec: VEventControl) (se: VPExpr)
  (** For sequenverilog_expr *)
  | VPExprExpr (e: VExpr)
  | VPExprInter (lse rse: VPExpr)
  | VPExprWithin (lse rse: VPExpr).

  (*! -- end of Expressions *)

  (*! Assignments -- *)

  (* net_assignment ::= net_lvalue = expression *)
  (* variable_assignment ::= variable_lvalue = expression *)
  Inductive VAssign :=
  | VAssignO (lv: VNetLValue) (e: VExpr).

  (* list_of_net_assignments ::= net_assignment { , net_assignment } *)
  (* list_of_variable_assignments ::= variable_assignment { , variable_assignment } *)
  Inductive VAssigns :=
  | VAssignsOne (na: VAssign)
  | VAssignsCons (na: VAssign)
                 (nas: VAssigns).
  Coercion VAssignsOne: VAssign >-> VAssigns.

  (* assignment_operator ::= *)
  (* = | += | -= | *= | /= | %= | &= | |= | ^= | <<= | >>= | <<<= | >>>= *)
  Inductive VAssignOp :=
  | VAsnOpEq | VAsnOpAdd | VAsnOpSub | VAsnOpMul | VAsnOpDiv | VAsnOpRem
  | VAsnOpBAnd | VAsnOpBOr | VAsnOpBXor | VAsnOpShl | VAsnOpShr | VAsnOpSal | VAsnOpSar.

  (* operator_assignment ::= variable_lvalue assignment_operator expression *)
  Inductive VOpAssign :=
  | VOpAssignO (lv: VVarLValue) (aop: VAssignOp) (e: VExpr).

  (*! -- end of Assignments *)

  (*! Ports -- *)

  (* port_direction ::= input | output | inout | ref *)
  Inductive VPortDirection :=
  | VPortDirectionInput
  | VPortDirectionOutput
  | VPortDirectionInout
  | VPortDirectionRef.

  (* net_type ::= supply0 | supply1 | tri | triand | trior | tri0 | tri1 | wire | wand | wor *)
  Inductive VNetType :=
  | VNetTypeWire.

  (* unpacked_dimension ::= [ constant_range ] | [ constant_expression ] *)
  (* packed_dimension ::= [ constant_range ] | unsized_dimension *)
  (* constant_range ::= constant_expression : constant_expression *)
  Inductive VDim :=
  | VDimRange (lr rr: VExpr)
  | VDimOne (de: VExpr).

  Inductive VPackedDims :=
  | VPackedDimsNil
  | VPackedDimsOne (pd: VDim)
  | VPackedDimsCons (pd: VDim) (pds: VPackedDims).
  Coercion VPackedDimsOne: VDim >-> VPackedDims.

  (* variable_dimension ::= *)
  (* (v)   { sized_or_unsized_dimension } *)
  (* | associative_dimension *)
  (* | queue_dimension *)
  (* sized_or_unsized_dimension ::= unpacked_dimension | unsized_dimension *)
  Definition VVarDims := VPackedDims.

  (* integer_vector_type ::= bit | logic | reg *)
  Inductive VIntVecType := VBit | VLogic | VReg.

  (* integer_atom_type ::= byte | shortint | int | longint | integer | time *)
  Inductive VIntAtomType := VByte | VShortInt | VLongInt | VInteger | VTime.

  (* data_type ::= *)
  (* (v)   integer_vector_type [ signing ] { packed_dimension } *)
  (* (v) | integer_atom_type [ signing ] *)
  (* | non_integer_type *)
  (* | struct_union [ packed [ signing ] ] { struct_union_member { struct_union_member } } *)
  (*     { packed_dimension } *)
  (* | enum [ enum_base_type ] { enum_name_declaration { , enum_name_declaration } } *)
  (* | string *)
  (* | chandle *)
  (* | virtual [ interface ] interfaverilog_identifier *)
  (* | [ class_scope | package_scope ] type_identifier { packed_dimension } *)
  (* | class_type *)
  (* | event *)
  (* | ps_covergroup_identifier *)
  Inductive VDataType :=
  | VDataTypeIntVec (ty: VIntVecType) (pd: VPackedDims)
  | VDataTypeIntAtom (ty: VIntAtomType).

  (* port_type ::= *)
  (* [ net_type_or_trireg ] [ signing ] { packed_dimension } *)
  Inductive VPortType :=
  | VPortTypeO (nt: option VNetType) (pd: VPackedDims).

  (* net_port_header ::= [ port_direction ] port_type *)
  Inductive VNetPortHeader :=
  | VNetPortHeaderO (pd: option VPortDirection)
                    (pt: VPortType).

  (* variable_port_header ::= [ port_direction ] data_type *)
  Inductive VVarPortHeader :=
  | VVarPortHeaderO (pd: option VPortDirection)
                    (dt: VDataType).

  (* list_of_port_identifiers ::= port_identifier { unpacked_dimension } *)
  (* { , port_identifier { unpacked_dimension } } *)
  Inductive VPortIds :=
  | VPortIdsOne (n: VId)
  | VPortIdsCons (n: VId) (pis: VPortIds).
  (** NOTE: cannot use this coercion as well, dropped when closing the section *)
  (* Coercion VPortIdsOne: VId >-> VPortIds. *)

  (* port_declaration ::= *)
  (* { attribute_instance } inout_declaration *)
  (* | { attribute_instance } input_declaration *)
  (* | { attribute_instance } output_declaration *)
  (* | { attribute_instance } ref_declaration *)
  (* | { attribute_instance } interfaverilog_port_declaration *)
  Inductive VPortDecl :=
  (* inout_declaration ::= inout port_type list_of_port_identifiers *)
  | VPortDeclInoutP (pt: VPortType) (pis: VPortIds)
  (* input_declaration ::= *)
  (*   input port_type list_of_port_identifiers *)
  (* | input data_type list_of_variable_identifiers *)
  | VPortDeclInputP (pt: VPortType) (pis: VPortIds)
  | VPortDeclInputD (dt: VDataType) (pis: VPortIds)
  (* output_declaration ::= *)
  (*   output port_type list_of_port_identifiers *)
  (* | output data_type list_of_variable_port_identifiers *)
  | VPortDeclOutputP (pt: VPortType) (pis: VPortIds)
  | VPortDeclOutputD (dt: VDataType) (pis: VPortIds).

  (* ansi_port_declaration ::= *)
  (* (v)   [ net_port_header | interfaverilog_port_header ] port_identifier { unpacked_dimension } *)
  (* (v) | [ variable_port_header ] port_identifier variable_dimension [ = constant_expression ] *)
  (* | [ net_port_header | variable_port_header ] . port_identifier ( [ expression ] ) *)
  Inductive VAnsiPortDecl :=
  | VAnsiPortDeclNet (nph: option VNetPortHeader) (pid: VId)
  | VAnsiPortDeclVar (vph: option VVarPortHeader) (pid: VId).

  (* list_of_port_declarations ::= *)
  (* ( [ { attribute_instance} ansi_port_declaration { , { attribute_instance} ansi_port_declaration } ] ) *)
  Inductive VAnsiPortDecls :=
  | VAnsiPortDeclNil
  | VAnsiPortDeclsOne (p: VAnsiPortDecl)
  | VAnsiPortDeclsCons (p: VAnsiPortDecl) (ps: VAnsiPortDecls).
  Coercion VAnsiPortDeclsOne: VAnsiPortDecl >-> VAnsiPortDecls.

  (*! -- end of Ports *)

  (*! Statements -- *)

  (* cond_predicate ::= expression_or_cond_pattern { && expression_or_cond_pattern } *)
  (* expression_or_cond_pattern ::= expression | cond_pattern *)
  (* cond_pattern ::= expression matches pattern *)
  Definition VCondPredicate := VExpr.

  (* procedural_timing_control ::= delay_control | event_control | cycle_delay *)
  Inductive VProcTimingControl :=
  | VProcTimingControlEvent (ec: VEventControl).
  Coercion VProcTimingControlEvent: VEventControl >-> VProcTimingControl.

  (* case_item ::= *)
  (*   expression { , expression } : statement_or_null *)
  (* | default [ : ] statement_or_null *)
  Inductive VCaseItem (Stmt: Set) :=
  (* | VCaseItemCase (ces: list VExpr) (st: Stmt) *)
  | VCaseItemCase (ce: VExpr) (st: Stmt)
  | VCaseItemDefault (st: Stmt).

  (* for_initialization ::= *)
  (*   list_of_variable_assignments *)
  (* | data_type list_of_variable_assignments { , data_type list_of_variable_assignments } *)
  Inductive VForInit :=
  | VForInitVarAssignsO (vas: VAssigns).
  Coercion VForInitVarAssignsO: VAssigns >-> VForInit.

  (* for_step ::= for_step_assignment { , for_step_assignment } *)
  (* for_step_assignment ::= operator_assignment | inc_or_dec_expression *)
  Inductive VForStep :=
  | VForStepOpAssign (oa: VOpAssign)
  | VForStepIncOrDec (iod: VIncOrDecExpr).
  Coercion VForStepOpAssign: VOpAssign >-> VForStep.
  Coercion VForStepIncOrDec: VIncOrDecExpr >-> VForStep.

  (* case_keyword ::= case | casez | casex *)
  Inductive VCaseType :=
  | VCaseTypeD | VCaseTypeZ | VCaseTypeX.

  (* statement_item ::= *)
  (* (v)   blocking_assignment ; *)
  (* (v) | nonblocking_assignment ; *)
  (* | procedural_continuous_assignment ; *)
  (* (v) | case_statement *)
  (* (v) | conditional_statement *)
  (* | inc_or_dec_expression ; *)
  (* | subroutine_call_statement *)
  (* | disable_statement *)
  (* | event_trigger *)
  (* (v) | loop_statement *)
  (* (v) | jump_statement *)
  (* | par_block *)
  (* (v) | procedural_timing_control_statement *)
  (* (v) | seq_block *)
  (* | wait_statement *)
  (* | procedural_assertion_statement *)
  (* | clocking_drive ; *)
  (* | randsequenverilog_statement *)
  (* | randcase_statement *)
  (* | expect_property_statement *)
  Inductive VStatementItem: Set :=
  (* blocking_assignment ::= *)
  (* (v)   variable_lvalue = delay_or_event_control expression *)
  (* | hierarchical_dynamic_array_variable_identifier = dynamic_array_new *)
  (* | [ implicit_class_handle . | class_scope | package_scope ] hierarchical_variable_identifier *)
  (*     select = class_new *)
  (* | operator_assignment *)
  | VStatementItemBlockingAssignNormal (vlv: VVarLValue) (e: VExpr)

  (* nonblocking_assignment ::= variable_lvalue <= [ delay_or_event_control ] expression *)
  | VStatementItemNonblockingAssign (vlv: VVarLValue) (e: VExpr)

  (* case_statement ::= *)
  (* (v)   [ unique_priority ] case_keyword ( expression ) case_item { case_item } endcase *)
  (* | [ unique_priority ] case_keyword ( expression ) matches case_pattern_item { case_pattern_item } endcase *)
  | VStatementCase (cty: VCaseType) (ce: VExpr) (css: list (VCaseItem VStatementItem))

  (* conditional_statement ::= *)
  (* (v)   if ( cond_predicate ) statement_or_null [ else statement_or_null ] *)
  (* | unique_priority_if_statement *)
  | VStatementCond (cp: VCondPredicate)
                   (ts: option VStatementItem) (* statement_or_null *)
                   (fs: option (option VStatementItem)) (* statement_or_null *)

  (* loop_statement ::= *)
  (* (v)   forever statement_or_null *)
  (* (v) | repeat ( expression ) statement_or_null *)
  (* (v) | while ( expression ) statement_or_null *)
  (* | for ( for_initialization ; expression ; for_step ) statement_or_null *)
  (* (v) | do statement_or_null while ( expression ) ; *)
  (* | foreach ( array_identifier [ loop_variables ] ) statement *)
  | VStatementItemForever (s: VStatementItem)
  | VStatementItemRepeat (re: VExpr) (s: VStatementItem)
  | VStatementItemWhile (we: VExpr) (s: VStatementItem)
  | VStatementItemFor (init: VForInit) (ce: VExpr) (step: VForStep) (s: VStatementItem)
  | VStatementItemDoWhile (s: VStatementItem) (we: VExpr)

  (* jump_statement ::= *)
  (* (v)   return [ expression ] ; *)
  (* | break ; *)
  (* | continue ; *)
  | VStatementItemReturn (re: VExpr)

  | VStatementProcTimingControl (ptc: VProcTimingControl) (s: VStatementItem)

  (* seq_block ::= *)
  (* begin [ : block_identifier ] { block_item_declaration } { statement_or_null } end [ : block_identifier ] *)
  | VStatementSeqBlock (ss: list VStatementItem).

  (* statement ::= [ block_identifier : ] { attribute_instance } statement_item *)
  Inductive VStatement :=
  | VStatementO (si: VStatementItem).
  Coercion VStatementO: VStatementItem >-> VStatement.

  (*! -- end of Statements *)

  (*! Module Items -- *)

  (* continuous_assign ::= *)
  (* (v)  assign [ drive_strength ] [ delay3 ] list_of_net_assignments ; *)
  (* | assign [ delay_control ] list_of_variable_assignments ; *)
  Inductive VContAssign :=
  | VContAssignNet (nas: VAssigns).

  Inductive VAlwaysKeyword := VAlways | VAlwaysComb | VAlwaysLatch | VAlwaysFF.

  (* data_type_or_implicit ::= data_type | [ signing ] { packed_dimension } *)
  Inductive VDataTypeOrImplicit :=
  | VDataTypeOrImplicitDat (dt: VDataType)
  | VDataTypeOrImplicitImp (pd: VPackedDims).

  (* variable_decl_assignment ::= *)
  (* (v)   variable_identifier variable_dimension [ = expression ] *)
  (* | dynamic_array_variable_identifier [ ] [ = dynamic_array_new ] *)
  (* | class_variable_identifier [ = class_new ] *)
  (* | [ covergroup_variable_identifier ] = new [ ( list_of_arguments ) ] *)
  Inductive VVarDeclAssign :=
  | VVarDeclAssignVar (vid: VId) (vd: VVarDims) (ve: option VExpr).

  (* list_of_variable_decl_assignments ::= variable_decl_assignment { , variable_decl_assignment } *)
  Inductive VVarDeclAssigns :=
  | VVarDeclAssignsOne (pa: VVarDeclAssign)
  | VVarDeclAssignsCons (pa: VVarDeclAssign) (pas: VVarDeclAssigns).
  Coercion VVarDeclAssignsOne: VVarDeclAssign >-> VVarDeclAssigns.

  (* variable_declaration ::= data_type list_of_variable_decl_assignments ; *)
  Inductive VVarDecl :=
  | VVarDeclOne (dt: VDataType) (vdas: VVarDeclAssigns).

  (* data_declaration ::= *)
  (* (v)   [ const ] [ lifetime ] variable_declaration *)
  (* | type_declaration *)
  (* | package_import_declaration *)
  (* | virtual_interfaverilog_declaration *)
  Inductive VDataDecl :=
  | VDataDeclVarDecl (vd: VVarDecl).
  Coercion VDataDeclVarDecl: VVarDecl >-> VDataDecl.

  (* param_assignment ::= parameter_identifier { unpacked_dimension } = constant_param_expression *)
  Inductive VParamAssign :=
  | VParamAssignOne (pid: VId) (cpe: VConstParamExpr).

  (* list_of_param_assignments ::= param_assignment { , param_assignment } *)
  Inductive VParamAssigns :=
  | VParamAssignsOne (pa: VParamAssign)
  | VParamAssignsCons (pa: VParamAssign) (pas: VParamAssigns).
  Coercion VParamAssignsOne: VParamAssign >-> VParamAssigns.

  (* parameter_declaration ::= *)
  (* (v)   parameter data_type_or_implicit list_of_param_assignments *)
  (* | parameter type list_of_type_assignments *)
  Inductive VParamDecl :=
  | VParamDeclData (dti: VDataTypeOrImplicit) (pas: VParamAssigns).

  (* local_parameter_declaration ::= *)
  (* (v) localparam data_type_or_implicit list_of_param_assignments ; *)
  Inductive VLocalParamDecl :=
  | VLocalParamDeclOne (dti: VDataTypeOrImplicit) (pas: VParamAssigns).

  (* net_decl_assignment ::= net_identifier { unpacked_dimension } [ = expression ] *)
  Inductive VNetDeclAssign :=
  | VNetDeclAssignOne (nid: VId) (ve: option VExpr).

  (* list_of_net_decl_assignments ::= net_decl_assignment { , net_decl_assignment } *)
  Inductive VNetDeclAssigns :=
  | VNetDeclAssignsOne (pa: VNetDeclAssign)
  | VNetDeclAssignsCons (pa: VNetDeclAssign) (pas: VNetDeclAssigns).
  Coercion VNetDeclAssignsOne: VNetDeclAssign >-> VNetDeclAssigns.

  (* net_declaration ::= *)
  (*   net_type_or_trireg [ drive_strength | charge_strength ] [ vectored | scalared ] *)
  (*   [ signing ] { packed_dimension } [ delay3 ] list_of_net_decl_assignments ; *)
  Inductive VNetDecl :=
  | VNetDeclOne (nt: VNetType) (pd: VPackedDims) (nda: VNetDeclAssigns).

  (** NOTE: tf_port_item differs a bit from ansi_port_decl, but it's still fine to reuse for certain purposes. *)
  (* tf_port_list ::= tf_port_item { , tf_port_item } *)
  Definition VTfPortList := VAnsiPortDecls.

  (* task_declaration ::= task [ lifetime ] task_body_declaration *)
  (* task_body_declaration ::= *)
  (*   [ interfaverilog_identifier . | class_scope ] task_identifier ; *)
  (*   { tf_item_declaration } *)
  (*   { statement_or_null } *)
  (*   endtask [ : task_identifier ] *)
  (* (v) | [ interfaverilog_identifier . | class_scope ] task_identifier ( [ tf_port_list ] ) ; *)
  (*   { block_item_declaration } *)
  (*   { statement_or_null } *)
  (*   endtask [ : task_identifier ] *)
  Inductive VTaskDecl :=
  | VTaskDeclOne (tid: VId) (st: VStatement).

  (* block_item_declaration ::= *)
  (*   { attribute_instance } data_declaration *)
  (* | { attribute_instance } local_parameter_declaration *)
  (* | { attribute_instance } parameter_declaration ; *)
  (* | { attribute_instance } overload_declaration *)
  (* Inductive VBlockItemDecl := . *)

  (* function_declaration ::= function [ lifetime ] function_body_declaration *)
  (* function_body_declaration ::=  *)
  (*       function_data_type_or_implicit *)
  (*       [ interfaverilog_identifier . | class_scope ] function_identifier ; { tf_item_declaration } *)
  (*       { function_statement_or_null } *)
  (*       endfunction [ : function_identifier ] *)
  (* (v) | function_data_type_or_implicit *)
  (*       [ interfaverilog_identifier . | class_scope ] function_identifier ( [ tf_port_list ] ) ; *)
  (*       { block_item_declaration } *)
  (*       { function_statement_or_null } endfunction [ : function_identifier ] *)
  Inductive VFuncDecl :=
  | VFuncDeclOne (dti: VDataTypeOrImplicit) (fid: VId)
                 (ports: VTfPortList)
                 (st: VStatement).

  (* package_or_generate_item_declaration ::= *)
  (* (v)   net_declaration *)
  (* (v) | data_declaration *)
  (* (v) | task_declaration *)
  (* (v) | function_declaration *)
  (* | dpi_import_export *)
  (* | extern_constraint_declaration *)
  (* | class_declaration *)
  (* | class_constructor_declaration *)
  (* (v) | parameter_declaration ; *)
  (* (v) | local_parameter_declaration *)
  (* | covergroup_declaration *)
  (* | overload_declaration *)
  (* | concurrent_assertion_item_declaration *)
  (* | ; *)
  Inductive VPkgGenItemDecl :=
  | VPkgGenItemDeclNet (nd: VNetDecl)
  | VPkgGenItemDeclData (dd: VDataDecl)
  | VPkgGenItemDeclTask (td: VTaskDecl)
  | VPkgGenItemDeclFunc (fd: VFuncDecl)
  | VPkgGenItemDeclParam (pd: VParamDecl)
  | VPkgGenItemDeclLocalParam (lpd: VLocalParamDecl).
  Coercion VPkgGenItemDeclNet: VNetDecl >-> VPkgGenItemDecl.
  Coercion VPkgGenItemDeclData: VDataDecl >-> VPkgGenItemDecl.
  Coercion VPkgGenItemDeclTask: VTaskDecl >-> VPkgGenItemDecl.
  Coercion VPkgGenItemDeclFunc: VFuncDecl >-> VPkgGenItemDecl.
  Coercion VPkgGenItemDeclParam: VParamDecl >-> VPkgGenItemDecl.
  Coercion VPkgGenItemDeclLocalParam: VLocalParamDecl >-> VPkgGenItemDecl.

  (* module_or_generate_item_declaration ::= *)
  (* (v)   package_or_generate_item_declaration *)
  (* | genvar_declaration *)
  (* | clocking_declaration *)
  (* | default clocking clocking_identifier ; *)
  Inductive VModuleGenItemDecl :=
  | VModuleGenItemDeclPkg (pd: VPkgGenItemDecl).
  Coercion VModuleGenItemDeclPkg: VPkgGenItemDecl >-> VModuleGenItemDecl.

  (** NOTE: it looks like event_control includes clocking_event? *)
  (* property_spec ::= [clocking_event ] [ disable iff ( expression_or_dist ) ] property_expr *)
  Inductive VPropSpec :=
  | VPropSpecO (oce: option VEventControl) (pe: VPExpr).

  (* concurrent_assertion_item ::= [ block_identifier : ] concurrent_assertion_statement *)
  (* concurrent_assertion_statement ::= *)
  (* | assert_property_statement *)
  (* | assume_property_statement *)
  (* | cover_property_statement *)
  (* assert_property_statement::= assert property ( property_spec ) action_block *)
  (* action_block ::= statement_or_null | [ statement ] else statement_or_null *)
  (* assume_property_statement::= assume property ( property_spec ) ; *)
  (* cover_property_statement::= cover property ( property_spec ) statement_or_null *)
  Inductive VConcurAssert :=
  | VAssertProp (ps: VPropSpec) (st: option VStatement)
  | VAssumeProp (ps: VPropSpec)
  | VCoverProp (ps: VPropSpec) (st: option VStatement).

  (* module_common_item ::= *)
  (* (v)   module_or_generate_item_declaration *)
  (* | interfaverilog_instantiation *)
  (* | program_instantiation *)
  (* (v) | concurrent_assertion_item *)
  (* | bind_directive *)
  (* (v) | continuous_assign *)
  (* | net_alias *)
  (* (v) | initial_construct *)
  (* | final_construct *)
  (* (v) | always_construct *)
  Inductive VModuleCommonItem :=
  | VModuleCommonItemDecl (md: VModuleGenItemDecl)
  | VModuleCommonItemAssert (ca: VConcurAssert)
  | VModuleCommonItemContAssign (a: VContAssign)
  | VModuleCommonItemInitial (st: VStatement)
  | VModuleCommonItemAlways (ak: VAlwaysKeyword) (st: VStatement).
  Coercion VModuleCommonItemDecl: VModuleGenItemDecl >-> VModuleCommonItem.
  Coercion VModuleCommonItemAssert: VConcurAssert >-> VModuleCommonItem.
  Coercion VModuleCommonItemContAssign: VContAssign >-> VModuleCommonItem.

  (* parameter_value_assignment ::= # ( list_of_parameter_assignments ) *)
  Inductive VParamValueAssigns :=
  | VParamValueAssignsNil.

  (* named_port_connection ::= *)
  (*   { attribute_instance } . port_identifier [ ( [ expression ] ) ] *)
  (* (v) | { attribute_instance } .* *)
  Inductive VNamedPortConn :=
  | VNamedPortConnI (pid: VId)
  | VNamedPortConnE (pid: VId) (e: VExpr)
  | VNamedPortConnW.

  Inductive VNamedPortConns :=
  | VNamedPortConnsOne (npc: VNamedPortConn)
  | VNamedPortConnsCons (npc: VNamedPortConn) (npcs: VNamedPortConns).
  Coercion VNamedPortConnsOne: VNamedPortConn >-> VNamedPortConns.

  (* list_of_port_connections ::= *)
  (*   ordered_port_connection { , ordered_port_connection } *)
  (* (v) | named_port_connection { , named_port_connection } *)
  Inductive VPortConns :=
  | VPortConnsNamed (npc: VNamedPortConns).
  Coercion VPortConnsNamed: VNamedPortConns >-> VPortConns.

  (* hierarchical_instance ::= name_of_instance ( [ list_of_port_connections ] ) *)
  (* name_of_instance ::= instanverilog_identifier { unpacked_dimension } *)
  Inductive VHierIns :=
  | VHierInsOne (iid: VId) (pcs: VPortConns).

  (** NOTE: currently only supports a single instantiation *)
  (* module_instantiation ::= *)
  (* module_identifier [ parameter_value_assignment ] hierarchical_instance { , hierarchical_instance } ; *)
  Inductive VModuleIns :=
  | VModuleInsOne (mid: VId) (pva: VParamValueAssigns) (mins: VHierIns).

  (* module_or_generate_item ::= *)
  (*   { attribute_instance } parameter_override *)
  (* | { attribute_instance } gate_instantiation *)
  (* | { attribute_instance } udp_instantiation *)
  (* (v) | { attribute_instance } module_instantiation *)
  (* (v) | { attribute_instance } module_common_item *)
  Inductive VModuleOrGenerateItem :=
  | VModuleOrGenerateItemIns (mi: VModuleIns)
  | VModuleOrGenerateItemCommon (ci: VModuleCommonItem).
  Coercion VModuleOrGenerateItemIns: VModuleIns >-> VModuleOrGenerateItem.
  Coercion VModuleOrGenerateItemCommon: VModuleCommonItem >-> VModuleOrGenerateItem.

  (* generate_module_item ::= *)
  (* (v)   generate_module_conditional_statement *)
  (* | generate_module_case_statement *)
  (* | generate_module_loop_statement *)
  (* (v) | [ generate_block_identifier : ] generate_module_block *)
  (* (v) | module_or_generate_item *)
  (* generate_module_conditional_statement ::= *)
  (*   if ( constant_expression ) generate_module_item [ else generate_module_item ] *)
  (* generate_module_block ::= *)
  (*   begin [ : generate_block_identifier ] { generate_module_item } end [ : generate_block_identifier ] *)
  Inductive VGenerateModuleItem :=
  | VGenerateModuleItemCond (ce: VExpr) (tgmi: VGenerateModuleItem) (fgmi: option VGenerateModuleItem)
  | VGenerateModuleItemBlock (gmi: list VGenerateModuleItem)
  | VGenerateModuleItemModule (mgi: VModuleOrGenerateItem).

  (* generated_module_instantiation ::= generate { generate_module_item } endgenerate *)
  Inductive VGeneratedModuleIns :=
  | VGeneratedModuleInsO (gmi: VGenerateModuleItem).

  (* non_port_module_item ::= *)
  (* (v)   generated_module_instantiation *)
  (* (v) | module_or_generate_item *)
  (* | specify_block *)
  (* | { attribute_instance } specparam_declaration *)
  (* | program_declaration *)
  (* | module_declaration *)
  (* | timeunits_declaration *)
  Inductive VNonPortModuleItem :=
  | VNonPortGeneratedModuleIns (gmi: VGeneratedModuleIns)
  | VNonPortModuleOrGenerateItem (mog: VModuleOrGenerateItem).
  Coercion VNonPortGeneratedModuleIns: VGeneratedModuleIns >-> VNonPortModuleItem.
  Coercion VNonPortModuleOrGenerateItem: VModuleOrGenerateItem >-> VNonPortModuleItem.

  Inductive VModuleItem :=
  | VModuleItemPortDecl (pd: VPortDecl)
  | VModuleItemNonPort (np: VNonPortModuleItem).
  Coercion VModuleItemPortDecl: VPortDecl >-> VModuleItem.
  Coercion VModuleItemNonPort: VNonPortModuleItem >-> VModuleItem.

  (* parameter_port_declaration ::= *)
  (* (v)   parameter_declaration *)
  (* | data_type list_of_param_assignments *)
  (* | type list_of_type_assignments *)
  (* parameter_port_list ::= *)
  (* (v)   # ( list_of_param_assignments { , parameter_port_declaration } ) *)
  (* (v) | # ( parameter_port_declaration { , parameter_port_declaration } ) *)
  Inductive VParamPorts :=
  | VParamPortsNil
  | VParamPortsOne (pd: VParamDecl)
  | VParamPortsCons (pd: VParamDecl) (pds: VParamPorts).
  Coercion VParamPortsOne: VParamDecl >-> VParamPorts.

  Inductive VModuleItems :=
  | VModuleItemsOne (i: VModuleItem)
  | VModuleItemsCons (i: VModuleItem)
                     (is: VModuleItems).
  Coercion VModuleItemsOne: VModuleItem >-> VModuleItems.

  (*! -- end of Module Items *)

  (* module_declaration ::= *)
  (*   module_nonansi_header [ timeunits_declaration ] { module_item } *)
  (*   endmodule [ : module_identifier ] *)
  (* (v) | module_ansi_header [ timeunits_declaration ] { non_port_module_item } *)
  (*       endmodule [ : module_identifier ] *)
  (* | { attribute_instance } module_keyword [ lifetime ] module_identifier ( .* ) ; *)
  (*   [ timeunits_declaration ] { module_item } endmodule [ : module_identifier ] *)
  (* | extern module_nonansi_header *)
  (* | extern module_ansi_header *)
  (* module_ansi_header ::= *)
  (*   { attribute_instance } module_keyword [ lifetime ] module_identifier [ parameter_port_list ] *)
  (*   [ list_of_port_declarations ] ; *)
  Inductive VModuleDecl :=
  | VModuleDeclAnsi (name: VId)
                    (params: VParamPorts)
                    (ports: VAnsiPortDecls)
                    (items: VModuleItems).

End VModuleDecl.

(*! Notations *)

(** verilog_lit *)

(** NOTE: Idk but operation conflicts in the VExpr level are avoided by setting literals
 * placed at level 2. *)
Notation "'b bv" := (VIntegralBinary None bv)
                      (in custom verilog_lit at level 0, bv constr at level 0,
                         format "''b' bv").
Notation "sz 'b bv" := (VIntegralBinary (Some sz) bv)
                         (in custom verilog_lit at level 0, sz constr at level 0, bv constr at level 0,
                         format "sz ''b' bv").

Notation "'o bv" := (VIntegralOctal None bv)
                      (in custom verilog_lit at level 0, bv constr at level 0,
                         format "''o' bv").
Notation "sz 'o bv" := (VIntegralOctal (Some sz) bv)
                         (in custom verilog_lit at level 0, sz constr at level 0, bv constr at level 0,
                         format "sz ''o' bv").

Notation "'h bv" := (VIntegralHex None bv)
                      (in custom verilog_lit at level 0, bv constr at level 0,
                         format "''h' bv").
Notation "sz 'h bv" := (VIntegralHex (Some sz) bv)
                         (in custom verilog_lit at level 0, sz constr at level 0, bv constr,
                         format "sz ''h' bv").

Notation "bv" := (VDecimalNumberNB bv)
                   (in custom verilog_lit at level 0, bv constr at level 0).
Notation "'d bv" := (VDecimalNumberB None bv)
                      (in custom verilog_lit at level 0, bv constr at level 0).
Notation "sz 'd bv" := (VDecimalNumberB (Some sz) bv)
                         (in custom verilog_lit at level 0, sz constr at level 0, bv constr,
                         format "sz ''d' bv").

Notation "'0" := VZeros (in custom verilog_lit at level 0).
Notation "'1" := VOnes (in custom verilog_lit at level 0).

(** verilog_pexpr *)

(* Custom-entry coercion from verilog_expr to verilog_pexpr *)
Notation "e" := (VPExprExpr e) (in custom verilog_pexpr at level 98, e custom verilog_expr at level 97).

Notation "( e )" := e (in custom verilog_pexpr, e at level 98).

Notation "'if' ( ce ) tpe" := (VPExprIfElse ce tpe None) (in custom verilog_pexpr at level 97).
Notation "'if' ( ce ) tpe 'else' fpe" := (VPExprIfElse ce tpe (Some fpe)) (in custom verilog_pexpr at level 97).
Notation "lpe '|->' rpe" := (VPExprImp lpe rpe) (in custom verilog_pexpr at level 96, left associativity).
Notation "lpe '|=>' rpe" := (VPExprImpN lpe rpe) (in custom verilog_pexpr at level 96, left associativity).
Notation "lpe '|=>' rpe" := (VPExprImpN lpe rpe) (in custom verilog_pexpr at level 96, left associativity).
Notation "lpe 'or' rpe" := (VPExprOr lpe rpe) (in custom verilog_pexpr at level 95, left associativity).
Notation "lpe 'and' rpe" := (VPExprAnd lpe rpe) (in custom verilog_pexpr at level 95, left associativity).
Notation "lpe 'intersect' rpe" := (VPExprInter lpe rpe) (in custom verilog_pexpr at level 95, left associativity).
Notation "lpe 'within' rpe" := (VPExprWithin lpe rpe) (in custom verilog_pexpr at level 95, left associativity).
Notation "'not' pe" := (VPExprNot pe) (in custom verilog_pexpr at level 94).
(* Notation "" := (VPExprClk ec se) (in custom verilog_pexpr at level 97). *)

(** verilog_expr *)

(** NOTE: coercion (VId >-> VExpr) doesn't work for (list VExpr) or (option VExpr), thus concatenations like
 * {id1, id2} doesn't work. In order to solve this issue, we explicitly define (econs) to say that each
 * element should be (VExpr). *)
Definition econs {VId} (e: @VExpr VId) (es: list VExpr): list VExpr := cons e es.
Definition SomeE {VId} (e: @VExpr VId): option VExpr := Some e.

(* Custom-entry coercion from verilog_lit to verilog_expr *)
Notation "p" := (VExprPriLiteral p) (in custom verilog_expr at level 0, p custom verilog_lit at level 0).

Notation "( e )" := e (in custom verilog_expr, e at level 99).

Notation "ce ? te : fe" := (VExprCond ce te fe) (in custom verilog_expr at level 94, right associativity).
Notation "le '||' re" := (VExprBinOp VBinLOr le re) (in custom verilog_expr at level 93, left associativity).
Notation "le '&&' re" := (VExprBinOp VBinLAnd le re) (in custom verilog_expr at level 92, left associativity).
Notation "le '|' re" := (VExprBinOp VBinBOr le re) (in custom verilog_expr at level 91, left associativity).
Notation "le '^' re" := (VExprBinOp VBinBXor le re) (in custom verilog_expr at level 90, left associativity).
Notation "le '^~' re" := (VExprBinOp VBinBXnor le re) (in custom verilog_expr at level 90, left associativity).
Notation "le '~^' re" := (VExprBinOp VBinBXnor le re) (in custom verilog_expr at level 90, left associativity).
Notation "le '&' re" := (VExprBinOp VBinBAnd le re) (in custom verilog_expr at level 89, left associativity).
Notation "le '===' re" := (VExprBinOp VBinFEq le re) (in custom verilog_expr at level 88, left associativity).
Notation "le '!==' re" := (VExprBinOp VBinFNEq le re) (in custom verilog_expr at level 88, left associativity).
Notation "le '=?=' re" := (VExprBinOp VBinWEq le re) (in custom verilog_expr at level 88, left associativity).
Notation "le '!?=' re" := (VExprBinOp VBinWNEq le re) (in custom verilog_expr at level 88, left associativity).
Notation "le '==' re" := (VExprBinOp VBinEq le re) (in custom verilog_expr at level 87, left associativity).
Notation "le '!=' re" := (VExprBinOp VBinNEq le re) (in custom verilog_expr at level 87, left associativity).
Notation "le '<' re" := (VExprBinOp VBinLt le re) (in custom verilog_expr at level 86, left associativity).

Notation "ie 'inside' { ce }" := (VExprInside ie (econs ce nil)) (in custom verilog_expr at level 86).
Notation "ie 'inside' { ce1 , .. , cen }" :=
  (VExprInside ie (econs ce1 .. (econs cen nil) ..)) (in custom verilog_expr at level 86).

Notation "le '<=' re" := (VExprBinOp VBinLe le re) (in custom verilog_expr at level 86, left associativity).
Notation "le '>' re" := (VExprBinOp VBinGt le re) (in custom verilog_expr at level 86, left associativity).
Notation "le '>=' re" := (VExprBinOp VBinGe le re) (in custom verilog_expr at level 86, left associativity).
Notation "le '>>' re" := (VExprBinOp VBinShr le re) (in custom verilog_expr at level 85, left associativity).
Notation "le '<<' re" := (VExprBinOp VBinShl le re) (in custom verilog_expr at level 85, left associativity).
Notation "le '>>>' re" := (VExprBinOp VBinSar le re) (in custom verilog_expr at level 85, left associativity).
Notation "le '<<<' re" := (VExprBinOp VBinSal le re) (in custom verilog_expr at level 85, left associativity).
Notation "le '+' re" := (VExprBinOp VBinAdd le re) (in custom verilog_expr at level 84, left associativity).
Notation "le '-' re" := (VExprBinOp VBinSub le re) (in custom verilog_expr at level 84, left associativity).
Notation "le '*' re" := (VExprBinOp VBinMul le re) (in custom verilog_expr at level 83, left associativity).
Notation "le '/' re" := (VExprBinOp VBinDiv le re) (in custom verilog_expr at level 83, left associativity).
Notation "le '%' re" := (VExprBinOp VBinRem le re) (in custom verilog_expr at level 83, left associativity).
Notation "le '**' re" := (VExprBinOp VBinPow le re) (in custom verilog_expr at level 82, left associativity).

Notation "te [ se ]" := (VExprPriSelect te se) (in custom verilog_expr at level 74).
Notation "se [ lr : rr ]" := (VExprPriSelectConstRange se lr rr) (in custom verilog_expr at level 74).
Notation "se [ lr +: rr ]" := (VExprPriSelectIdxRangeAdd se lr rr) (in custom verilog_expr at level 74).
Notation "se [ lr -: rr ]" := (VExprPriSelectIdxRangeSub se lr rr) (in custom verilog_expr at level 74).

Notation "'++' i" := (VIncExpr i) (in custom verilog_expr at level 78).
Notation "i '++'" := (VIncExpr i) (in custom verilog_expr at level 78).
Notation "'--' i" := (VDecExpr i) (in custom verilog_expr at level 78).
Notation "i '--'" := (VDecExpr i) (in custom verilog_expr at level 78).

Notation "'+' e" := (VExprUniOp VUniPlus e) (in custom verilog_expr at level 78).
Notation "'-' e" := (VExprUniOp VUniMinus e) (in custom verilog_expr at level 78).

Notation "'!' e" := (VExprUniOp VUniNot e) (in custom verilog_expr at level 77).
Notation "'~' e" := (VExprUniOp VUniNeg e) (in custom verilog_expr at level 77).
Notation "'&' e" := (VExprUniOp VUniAnd e) (in custom verilog_expr at level 77).
Notation "'|' e" := (VExprUniOp VUniOr e) (in custom verilog_expr at level 77).
Notation "'~&' e" := (VExprUniOp VUniNand e) (in custom verilog_expr at level 77).
Notation "'~|' e" := (VExprUniOp VUniNor e) (in custom verilog_expr at level 77).
Notation "'^' e" := (VExprUniOp VUniXor e) (in custom verilog_expr at level 77).
Notation "'~^' e" := (VExprUniOp VUniXnor e) (in custom verilog_expr at level 77).
Notation "'^~' e" := (VExprUniOp VUniXnor e) (in custom verilog_expr at level 77).

(** NOTE: no dots (.) for parsing; see the hack used around the tester defined below. *)
Notation "pe ce" := (VExprHier pe ce) (in custom verilog_expr at level 72, left associativity).
Notation "pe '.' ce" := (VExprHier pe ce) (in custom verilog_expr at level 72, left associativity,
  format "pe '.' ce").

Notation "'{}'" := (VExprPriConcat nil) (in custom verilog_expr at level 70).
Notation "'{' '}'" := (VExprPriConcat nil) (in custom verilog_expr at level 70).

Notation "'{' ne '{' se '}' '}'" := (VExprPriMultConcat ne (econs se nil)) (in custom verilog_expr at level 70).
Notation "'{' ne '{' se1 , .. , sen '}' '}'" :=
  (VExprPriMultConcat ne (econs se1 .. (econs sen nil) ..)) (in custom verilog_expr at level 70).

Notation "'{' se '}'" := (VExprPriConcat (econs se nil)) (in custom verilog_expr at level 70).
Notation "'{' se1 , .. , sen '}'" :=
  (VExprPriConcat (econs se1 .. (econs sen nil) ..)) (in custom verilog_expr at level 70).

Notation "sz '( e )" := (VExprCast sz e) (in custom verilog_expr at level 70).

Notation "tfid ( ae )" := (VExprTfCall tfid (econs ae nil)) (in custom verilog_expr at level 69).
Notation "tfid ( ae1 , .. , aen )" := (VExprTfCall tfid (econs ae1 .. (econs aen nil) ..)) (in custom verilog_expr at level 69).

Notation "'$signed' ( ae )" := (VExprSystemTfCall VSystemTfSigned (econs ae nil)) (in custom verilog_expr at level 69).
Notation "'$unsigned' ( ae )" := (VExprSystemTfCall VSystemTfUnsigned (econs ae nil)) (in custom verilog_expr at level 69).

(** verilog_packeddim *)

Notation "[ de ]" := (VDimOne de) (in custom verilog_packeddim at level 92, de custom verilog_expr at level 91).
Notation "[ lr : rr ]" := (VDimRange lr rr)
                            (in custom verilog_packeddim at level 92,
                                lr custom verilog_expr at level 91,
                                rr custom verilog_expr at level 91).

Notation "pd pds" := (VPackedDimsCons pd pds)
                       (in custom verilog_packeddim at level 93, right associativity).

(** verilog_stmt *)

Notation "'posedge' e" := (VEventExprExpr (Some VPosedge) e)
                            (in custom verilog_stmt at level 96, e custom verilog_expr at level 95).
Notation "'negedge' e" := (VEventExprExpr (Some VNegedge) e)
                            (in custom verilog_stmt at level 96, e custom verilog_expr at level 95).

(** NOTE: level of vlv and e should be smaller than the one for the (<=) operation in verilog_expr. *)
Notation "vlv = e ;" := (VStatementItemBlockingAssignNormal vlv e)
                          (in custom verilog_stmt at level 97,
                              vlv custom verilog_expr at level 80,
                              e custom verilog_expr at level 80).
Notation "vlv <= e ;" := (VStatementItemNonblockingAssign vlv e)
                           (in custom verilog_stmt at level 97,
                               vlv custom verilog_expr at level 80,
                               e custom verilog_expr at level 80).

Notation "'case' ( ce ) c1 .. cn 'endcase'" :=
  (VStatementCase VCaseTypeD ce (cons c1 .. (cons cn nil) ..))
    (in custom verilog_stmt at level 97, ce custom verilog_expr at level 96).
Notation "'casex' ( ce ) c1 .. cn 'endcase'" :=
  (VStatementCase VCaseTypeX ce (cons c1 .. (cons cn nil) ..))
    (in custom verilog_stmt at level 97, ce custom verilog_expr at level 96).
Notation "'casez' ( ce ) c1 .. cn 'endcase'" :=
  (VStatementCase VCaseTypeZ ce (cons c1 .. (cons cn nil) ..))
    (in custom verilog_stmt at level 97, ce custom verilog_expr at level 96).

(** NOTE: since the "case" items belong to verilog_stmt, in the below notation the level of `ce` should not
 * be larger than the ones in `vlv = e;` and `vlv <= e;`.
 *)
(* Notation "ce : st" := (VCaseItemCase VStatementItem (econs ce nil) st) *)
Notation "ce : st" := (VCaseItemCase VStatementItem ce st)
                        (in custom verilog_stmt at level 97,
                            ce custom verilog_expr at level 80,
                            st custom verilog_stmt at level 97).
(* Notation "ce1 , .. , cen : st" := (VCaseItemCase VStatementItem (econs ce1 .. (econs cen nil) ..) st) *)
(*                                     (in custom verilog_stmt at level 97, *)
(*                                         ce1 custom verilog_expr at level 80, *)
(*                                         cen custom verilog_expr at level 80, *)
(*                                         st custom verilog_stmt at level 97). *)

Notation "'default' : st" := (VCaseItemDefault VStatementItem st) (in custom verilog_stmt at level 96).

Notation "'if' ( cp ) tsn" := (VStatementCond cp (Some tsn) None)
                                (in custom verilog_stmt at level 97,
                                    cp custom verilog_expr,
                                    tsn custom verilog_stmt at level 97).
Notation "'if' ( cp ) tsn 'else' fsn" := (VStatementCond cp (Some tsn) (Some (Some fsn)))
                                           (in custom verilog_stmt at level 97,
                                               cp custom verilog_expr,
                                               tsn custom verilog_stmt at level 97,
                                               fsn custom verilog_stmt at level 97).
Notation "'forever' sn" := (VStatementItemForever sn) (in custom verilog_stmt at level 97).
Notation "'repeat' ( re ) sn" := (VStatementItemRepeat re sn)
                                   (in custom verilog_stmt at level 97, re custom verilog_expr at level 96).
Notation "'while' ( we ) sn" := (VStatementItemWhile we sn)
                                  (in custom verilog_stmt at level 97, we custom verilog_expr at level 96).
Notation "'for' ( init ; ce ; step ) sn" := (VStatementItemFor init ce step sn)
                                              (in custom verilog_stmt at level 97,
                                                  init custom verilog_assign at level 96,
                                                  ce custom verilog_expr at level 96,
                                                  step custom verilog_blockingassign at level 96).
Notation "'do' sn 'while' ( we )" := (VStatementItemDoWhile sn we)
                                       (in custom verilog_stmt at level 97, we custom verilog_expr at level 96).

Notation "'return' re ;" := (VStatementItemReturn re)
                              (in custom verilog_stmt at level 97, re custom verilog_expr at level 96).

Notation "@ ( ee ) sn" := (VStatementProcTimingControl ee sn) (in custom verilog_stmt at level 97).
Notation "@ '*' sn" := (VStatementProcTimingControl VEventControlAny sn) (in custom verilog_stmt at level 97).
(** NOTE: cannot cover ( * ) since the one without whitespaces is a comment notation in Coq! *)
(* Notation "@ '( * )' sn" := (VStatementProcTimingControl VEventControlAny sn) (in custom verilog_stmt at level 97). *)

Notation "'begin' 'end'" := (VStatementSeqBlock nil) (in custom verilog_stmt at level 97).
Notation "'begin' s 'end'" := (VStatementSeqBlock (cons s nil)) (in custom verilog_stmt at level 97).
Notation "'begin' s1 .. sn 'end'" := (VStatementSeqBlock (cons s1 .. (cons sn nil) ..))
                                       (in custom verilog_stmt at level 97).

(** verilog_assign *)

Notation "lv = e" := (VAssignO lv e)
                       (in custom verilog_assign at level 95,
                           lv custom verilog_expr, e custom verilog_expr).
Notation "na , nas" := (VAssignsCons na nas)
                         (in custom verilog_assign at level 96, right associativity).

(** verilog_blockingassign *)

(* Custom-entry coercion from verilog_expr to verilog_blockingassign *)
Notation "e" := e (in custom verilog_blockingassign at level 95, e custom verilog_expr at level 94).

Notation "lv '=' e" := (VOpAssignO lv VAsnOpEq e) (in custom verilog_blockingassign at level 95,
                                                      lv custom verilog_expr at level 94,
                                                      e custom verilog_expr at level 94).
Notation "lv '+=' e" := (VOpAssignO lv VAsnOpAdd e) (in custom verilog_blockingassign at level 95,
                                                        lv custom verilog_expr at level 94,
                                                        e custom verilog_expr at level 94).
Notation "lv '-=' e" := (VOpAssignO lv VAsnOpSub e) (in custom verilog_blockingassign at level 95,
                                                        lv custom verilog_expr at level 94,
                                                        e custom verilog_expr at level 94).
Notation "lv '*=' e" := (VOpAssignO lv VAsnOpMul e) (in custom verilog_blockingassign at level 95,
                                                        lv custom verilog_expr at level 94,
                                                        e custom verilog_expr at level 94).
Notation "lv '/=' e" := (VOpAssignO lv VAsnOpDiv e) (in custom verilog_blockingassign at level 95,
                                                        lv custom verilog_expr at level 94,
                                                        e custom verilog_expr at level 94).
Notation "lv '%=' e" := (VOpAssignO lv VAsnOpRem e) (in custom verilog_blockingassign at level 95,
                                                        lv custom verilog_expr at level 94,
                                                        e custom verilog_expr at level 94).
Notation "lv '&=' e" := (VOpAssignO lv VAsnOpBAnd e) (in custom verilog_blockingassign at level 95,
                                                         lv custom verilog_expr at level 94,
                                                         e custom verilog_expr at level 94).
Notation "lv '|=' e" := (VOpAssignO lv VAsnOpBOr e) (in custom verilog_blockingassign at level 95,
                                                        lv custom verilog_expr at level 94,
                                                        e custom verilog_expr at level 94).
Notation "lv '^=' e" := (VOpAssignO lv VAsnOpBXor e) (in custom verilog_blockingassign at level 95,
                                                         lv custom verilog_expr at level 94,
                                                         e custom verilog_expr at level 94).
Notation "lv '<<=' e" := (VOpAssignO lv VAsnOpShl e) (in custom verilog_blockingassign at level 95,
                                                         lv custom verilog_expr at level 94,
                                                         e custom verilog_expr at level 94).
Notation "lv '>>=' e" := (VOpAssignO lv VAsnOpShr e) (in custom verilog_blockingassign at level 95,
                                                         lv custom verilog_expr at level 94,
                                                         e custom verilog_expr at level 94).
Notation "lv '<<<=' e" := (VOpAssignO lv VAsnOpSal e) (in custom verilog_blockingassign at level 95,
                                                          lv custom verilog_expr at level 94,
                                                          e custom verilog_expr at level 94).
Notation "lv '>>>=' e" := (VOpAssignO lv VAsnOpSar e) (in custom verilog_blockingassign at level 95,
                                                          lv custom verilog_expr at level 94,
                                                          e custom verilog_expr at level 94).

(** verilog_netdeclassign *)

Notation "vid" := (VNetDeclAssignOne vid None)
                    (in custom verilog_netdeclassign at level 94, vid custom verilog_expr at level 94).
Notation "vid = ve" := (VNetDeclAssignOne vid (SomeE ve)) (** NOTE: search for SomeE why we need it. *)
                         (in custom verilog_netdeclassign at level 94,
                             vid custom verilog_expr at level 94,
                             ve custom verilog_expr at level 94).
Notation "va , vas" := (VNetDeclAssignsCons va vas)
                         (in custom verilog_netdeclassign at level 94, right associativity).

(** verilog_vardeclassign *)

Notation "vid" := (VVarDeclAssignVar vid VPackedDimsNil None)
                    (in custom verilog_vardeclassign at level 93, vid custom verilog_expr at level 93).
Notation "vid vd" := (VVarDeclAssignVar vid vd None)
                       (in custom verilog_vardeclassign at level 93,
                           vd custom verilog_packeddim at level 93,
                           vid custom verilog_expr at level 93).
Notation "va , vas" := (VVarDeclAssignsCons va vas)
                         (in custom verilog_vardeclassign at level 93, right associativity).

(** verilog_paramassign *)

Notation "pid = cpe" := (VParamAssignOne pid cpe)
                          (in custom verilog_paramassign at level 97,
                              pid custom verilog_expr, cpe custom verilog_expr).
Notation "pa , pas" := (VParamAssignsCons pa pas)
                         (in custom verilog_paramassign at level 97, right associativity).

(** verilog_paramports *)

(** NOTE: may want to share notations with verilog_paramassign; so many variants for parameters
 * thus it'd be better to share with them. *)

Notation "'parameter' pid = cpe" :=
  (VParamDeclData (VDataTypeOrImplicitImp VPackedDimsNil) (VParamAssignOne pid cpe))
    (in custom verilog_paramports at level 98,
        pid custom verilog_expr, cpe custom verilog_expr).
Notation "'parameter' pds pid = cpe" :=
  (VParamDeclData (VDataTypeOrImplicitImp pds) (VParamAssignOne pid cpe))
    (in custom verilog_paramports at level 98,
        pds custom verilog_packeddim,
        pid custom verilog_expr,
        cpe custom verilog_expr).
Notation "'parameter' 'integer' pid = cpe" :=
  (VParamDeclData (VDataTypeOrImplicitDat (VDataTypeIntAtom VInteger)) (VParamAssignOne pid cpe))
    (in custom verilog_paramports at level 98,
        pid custom verilog_expr,
        cpe custom verilog_expr).

Notation "pd , pds" := (VParamPortsCons pd pds)
                         (in custom verilog_paramports at level 99, right associativity).

(** verilog_ports *)

Notation "pid" :=
  (VAnsiPortDeclNet
     (Some (VNetPortHeaderO None (VPortTypeO None VPackedDimsNil)))
     pid)
    (in custom verilog_ports at level 95, pid custom verilog_expr at level 94).

Notation "'input' pid" :=
  (VAnsiPortDeclNet
     (Some (VNetPortHeaderO (Some VPortDirectionInput) (VPortTypeO None VPackedDimsNil)))
     pid)
    (in custom verilog_ports at level 95, pid custom verilog_expr at level 94).
Notation "'input' 'wire' pid" :=
  (VAnsiPortDeclNet
     (Some (VNetPortHeaderO (Some VPortDirectionInput) (VPortTypeO (Some VNetTypeWire) VPackedDimsNil)))
     pid)
    (in custom verilog_ports at level 95, pid custom verilog_expr at level 94).
Notation "'input' 'reg' pid" :=
  (VAnsiPortDeclVar
     (Some (VVarPortHeaderO (Some VPortDirectionInput) (VDataTypeIntVec VReg VPackedDimsNil)))
     pid)
    (in custom verilog_ports at level 95, pid custom verilog_expr at level 94).
Notation "'input' 'logic' pid" :=
  (VAnsiPortDeclVar
     (Some (VVarPortHeaderO (Some VPortDirectionInput) (VDataTypeIntVec VLogic VPackedDimsNil)))
     pid)
    (in custom verilog_ports at level 95, pid custom verilog_expr at level 94).

Notation "'input' pd pid" :=
  (VAnsiPortDeclNet
     (Some (VNetPortHeaderO (Some VPortDirectionInput) (VPortTypeO None pd)))
     pid)
    (in custom verilog_ports at level 95, pd custom verilog_packeddim at level 94, pid custom verilog_expr at level 94).
Notation "'input' 'wire' pd pid" :=
  (VAnsiPortDeclNet
     (Some (VNetPortHeaderO (Some VPortDirectionInput) (VPortTypeO (Some VNetTypeWire) pd)))
     pid)
    (in custom verilog_ports at level 95, pd custom verilog_packeddim at level 94, pid custom verilog_expr at level 94).
Notation "'input' 'reg' pd pid" :=
  (VAnsiPortDeclVar
     (Some (VVarPortHeaderO (Some VPortDirectionInput) (VDataTypeIntVec VReg pd)))
     pid)
    (in custom verilog_ports at level 95, pd custom verilog_packeddim at level 94, pid custom verilog_expr at level 94).
Notation "'input' 'logic' pd pid" :=
  (VAnsiPortDeclVar
     (Some (VVarPortHeaderO (Some VPortDirectionInput) (VDataTypeIntVec VLogic pd)))
     pid)
    (in custom verilog_ports at level 95, pd custom verilog_packeddim at level 94, pid custom verilog_expr at level 94).

Notation "'output' pid" :=
  (VAnsiPortDeclNet
     (Some (VNetPortHeaderO (Some VPortDirectionOutput) (VPortTypeO None VPackedDimsNil)))
     pid)
    (in custom verilog_ports at level 95, pid custom verilog_expr at level 94).
Notation "'output' 'wire' pid" :=
  (VAnsiPortDeclNet
     (Some (VNetPortHeaderO (Some VPortDirectionOutput) (VPortTypeO (Some VNetTypeWire) VPackedDimsNil)))
     pid)
    (in custom verilog_ports at level 95, pid custom verilog_expr at level 94).
Notation "'output' 'reg' pid" :=
  (VAnsiPortDeclVar
     (Some (VVarPortHeaderO (Some VPortDirectionOutput) (VDataTypeIntVec VReg VPackedDimsNil)))
     pid)
    (in custom verilog_ports at level 95, pid custom verilog_expr at level 94).
Notation "'output' 'logic' pid" :=
  (VAnsiPortDeclVar
     (Some (VVarPortHeaderO (Some VPortDirectionOutput) (VDataTypeIntVec VLogic VPackedDimsNil)))
     pid)
    (in custom verilog_ports at level 95, pid custom verilog_expr at level 94).

Notation "'output' pd pid" :=
  (VAnsiPortDeclNet
     (Some (VNetPortHeaderO (Some VPortDirectionOutput) (VPortTypeO None pd)))
     pid)
    (in custom verilog_ports at level 95, pd custom verilog_packeddim at level 94, pid custom verilog_expr at level 94).
Notation "'output' 'wire' pd pid" :=
  (VAnsiPortDeclNet
     (Some (VNetPortHeaderO (Some VPortDirectionOutput) (VPortTypeO (Some VNetTypeWire) pd)))
     pid)
    (in custom verilog_ports at level 95, pd custom verilog_packeddim at level 94, pid custom verilog_expr at level 94).
Notation "'output' 'reg' pd pid" :=
  (VAnsiPortDeclVar
     (Some (VVarPortHeaderO (Some VPortDirectionOutput) (VDataTypeIntVec VReg pd)))
     pid)
    (in custom verilog_ports at level 95, pd custom verilog_packeddim at level 94, pid custom verilog_expr at level 94).
Notation "'output' 'logic' pd pid" :=
  (VAnsiPortDeclVar
     (Some (VVarPortHeaderO (Some VPortDirectionOutput) (VDataTypeIntVec VLogic pd)))
     pid)
    (in custom verilog_ports at level 95, pd custom verilog_packeddim at level 94, pid custom verilog_expr at level 94).

Notation "p , ps" := (VAnsiPortDeclsCons p ps)
                       (in custom verilog_ports at level 96, right associativity).

(** verilog_gen *)

(** NOTE: the level should be smaller than the one for VModuleItemsCons. *)
Notation "mgi" := (VGenerateModuleItemModule mgi) (in custom verilog_gen at level 98,
                                                      mgi custom verilog_module at level 98).

Definition gcons {VId} (gmi: @VGenerateModuleItem VId) (gmis: list VGenerateModuleItem)
  : list VGenerateModuleItem := cons gmi gmis.
Notation "'begin' 'end'" := (VGenerateModuleItemBlock nil) (in custom verilog_gen at level 98).
Notation "'begin' s 'end'" := (VGenerateModuleItemBlock (gcons s nil)) (in custom verilog_gen at level 98).
Notation "'begin' s1 .. sn 'end'" := (VGenerateModuleItemBlock (gcons s1 .. (gcons sn nil) ..))
                                       (in custom verilog_gen at level 98).

Notation "'if' ( ce ) tgmi" := (VGenerateModuleItemCond ce tgmi None)
                                 (in custom verilog_gen at level 98,
                                     ce custom verilog_expr at level 98,
                                     tgmi custom verilog_gen at level 98).
Notation "'if' ( ce ) tgmi 'else' fgmi" := (VGenerateModuleItemCond ce tgmi (Some fgmi))
                                             (in custom verilog_gen at level 98,
                                                 ce custom verilog_expr at level 98,
                                                 tgmi custom verilog_gen at level 98,
                                                 fgmi custom verilog_gen at level 98).

(** verilog_module *)

Notation "'.*'" := VNamedPortConnW (in custom verilog_portconn).
Notation "pcid" := (VNamedPortConnI pcid)
                     (in custom verilog_portconn at level 96,
                         pcid custom verilog_portconnid at level 94).
Notation "pcid '()'" := (VNamedPortConnI pcid)
                          (in custom verilog_portconn at level 96,
                              pcid custom verilog_portconnid at level 94).
(** NOTE: interestingly ( ) cannot cover () *)
Notation "pcid '(' ')'" := (VNamedPortConnI pcid)
                             (in custom verilog_portconn at level 96,
                                 pcid custom verilog_portconnid at level 94).
Notation "pcid '(' e ')'" := (VNamedPortConnE pcid e)
                               (in custom verilog_portconn at level 96,
                                   pcid custom verilog_portconnid at level 94,
                                   e custom verilog_expr at level 94).
Notation "pc , pcs" := (VNamedPortConnsCons pc pcs)
                         (in custom verilog_portconn at level 97, right associativity).

Notation "'input' pis ;" := (VPortDeclInputP (VPortTypeO None VPackedDimsNil) pis)
                              (in custom verilog_module at level 98, pis custom verilog_expr at level 94).
Notation "'input' 'wire' pis ;" := (VPortDeclInputP (VPortTypeO (Some VNetTypeWire) VPackedDimsNil) pis)
                                     (in custom verilog_module at level 98, pis custom verilog_expr at level 94).
Notation "'input' 'reg' pis ;" := (VPortDeclInputD (VDataTypeIntVec VReg VPackedDimsNil) pis)
                                    (in custom verilog_module at level 98, pis custom verilog_expr at level 94).
Notation "'input' pd pis ;" := (VPortDeclInputP (VPortTypeO None pd) pis)
                                 (in custom verilog_module at level 98,
                                     pd custom verilog_packeddim at level 94,
                                     pis custom verilog_expr at level 94).
Notation "'input' 'wire' pd pis ;" := (VPortDeclInputP (VPortTypeO (Some VNetTypeWire) pd) pis)
                                        (in custom verilog_module at level 98,
                                            pd custom verilog_packeddim at level 94,
                                            pis custom verilog_expr at level 94).
Notation "'input' 'reg' pd pis ;" := (VPortDeclInputD (VDataTypeIntVec VReg pd) pis)
                                       (in custom verilog_module at level 98,
                                           pd custom verilog_packeddim at level 94,
                                           pis custom verilog_expr at level 94).

Notation "'output' pis ;" := (VPortDeclOutputP (VPortTypeO None VPackedDimsNil) pis)
                               (in custom verilog_module at level 98, pis custom verilog_expr at level 94).
Notation "'output' 'wire' pis ;" := (VPortDeclOutputP (VPortTypeO (Some VNetTypeWire) VPackedDimsNil) pis)
                                      (in custom verilog_module at level 98, pis custom verilog_expr at level 94).
Notation "'output' 'reg' pis ;" := (VPortDeclOutputD (VDataTypeIntVec VReg VPackedDimsNil) pis)
                                     (in custom verilog_module at level 98, pis custom verilog_expr at level 94).
Notation "'output' pd pis ;" := (VPortDeclOutputP (VPortTypeO None pd) pis)
                                  (in custom verilog_module at level 98,
                                      pd custom verilog_packeddim at level 94,
                                      pis custom verilog_expr at level 94).
Notation "'output' 'wire' pd pis ;" := (VPortDeclOutputP (VPortTypeO (Some VNetTypeWire) pd) pis)
                                         (in custom verilog_module at level 98,
                                             pd custom verilog_packeddim at level 94,
                                             pis custom verilog_expr at level 94).
Notation "'output' 'reg' pd pis ;" := (VPortDeclOutputD (VDataTypeIntVec VReg pd) pis)
                                        (in custom verilog_module at level 98,
                                            pd custom verilog_packeddim at level 94,
                                            pis custom verilog_expr at level 94).

Notation "'parameter' pas ;" := (VParamDeclData (VDataTypeOrImplicitImp VPackedDimsNil) pas)
                                  (in custom verilog_module at level 98, pas custom verilog_paramassign).
Notation "'parameter' 'integer' pas ;" := (VParamDeclData (VDataTypeOrImplicitDat (VDataTypeIntAtom VInteger)) pas)
                                            (in custom verilog_module at level 98, pas custom verilog_paramassign).

Notation "'localparam' pas ;" := (VLocalParamDeclOne (VDataTypeOrImplicitImp VPackedDimsNil) pas)
                                   (in custom verilog_module at level 98, pas custom verilog_paramassign).
Notation "'localparam' pd pas ;" := (VLocalParamDeclOne (VDataTypeOrImplicitImp pd) pas)
                                      (in custom verilog_module at level 98,
                                          pd custom verilog_packeddim,
                                          pas custom verilog_paramassign).
Notation "'localparam' 'integer' pas ;" := (VLocalParamDeclOne (VDataTypeOrImplicitDat (VDataTypeIntAtom VInteger)) pas)
                                             (in custom verilog_module at level 98, pas custom verilog_paramassign).

Notation "'bit' vdas ;" := (VVarDeclOne (VDataTypeIntVec VBit VPackedDimsNil) vdas)
                             (in custom verilog_module at level 98,
                                 vdas custom verilog_vardeclassign at level 94).
Notation "'bit' pd vdas ;" := (VVarDeclOne (VDataTypeIntVec VBit pd) vdas)
                                (in custom verilog_module at level 98,
                                    pd custom verilog_packeddim at level 94,
                                    vdas custom verilog_vardeclassign at level 94).
Notation "'logic' vdas ;" := (VVarDeclOne (VDataTypeIntVec VLogic VPackedDimsNil) vdas)
                               (in custom verilog_module at level 98,
                                   vdas custom verilog_vardeclassign at level 94).
Notation "'logic' pd vdas ;" := (VVarDeclOne (VDataTypeIntVec VLogic pd) vdas)
                                  (in custom verilog_module at level 98,
                                      pd custom verilog_packeddim at level 94,
                                      vdas custom verilog_vardeclassign at level 94).
Notation "'reg' vdas ;" := (VVarDeclOne (VDataTypeIntVec VReg VPackedDimsNil) vdas)
                             (in custom verilog_module at level 98,
                                 vdas custom verilog_vardeclassign at level 94).
Notation "'reg' pd vdas ;" := (VVarDeclOne (VDataTypeIntVec VReg pd) vdas)
                                (in custom verilog_module at level 98,
                                    pd custom verilog_packeddim at level 94,
                                    vdas custom verilog_vardeclassign at level 94).

Notation "'int' vdas ;" := (VVarDeclOne (VDataTypeIntAtom VInteger) vdas)
                             (in custom verilog_module at level 98,
                                 vdas custom verilog_vardeclassign at level 94).
Notation "'integer' vdas ;" := (VVarDeclOne (VDataTypeIntAtom VInteger) vdas)
                                 (in custom verilog_module at level 98,
                                     vdas custom verilog_vardeclassign at level 94).

Notation "'wire' ndas ;" := (VNetDeclOne VNetTypeWire VPackedDimsNil ndas)
                              (in custom verilog_module at level 98,
                                  ndas custom verilog_netdeclassign at level 94).
Notation "'wire' pd ndas ;" := (VNetDeclOne VNetTypeWire pd ndas)
                                 (in custom verilog_module at level 98,
                                     pd custom verilog_packeddim at level 94,
                                     ndas custom verilog_netdeclassign at level 94).

Notation "'assign' nas ;" := (VContAssignNet nas)
                               (in custom verilog_module at level 97, nas custom verilog_assign).

Notation "'task' tid ; st 'endtask'" := (VTaskDeclOne tid st)
                                          (in custom verilog_module at level 98,
                                              tid custom verilog_expr at level 97,
                                              st custom verilog_stmt at level 97).

Notation "'function' pd fid '(' ports ')' ; st 'endfunction'" := (VFuncDeclOne (VDataTypeOrImplicitImp pd) fid ports st)
                                                                   (in custom verilog_module at level 98,
                                                                       pd custom verilog_packeddim at level 97,
                                                                       fid custom verilog_expr at level 68,
                                                                       ports custom verilog_ports at level 68,
                                                                       st custom verilog_stmt at level 97).

Notation "'initial' st" := (VModuleCommonItemInitial st)
                            (in custom verilog_module at level 98, st custom verilog_stmt at level 97).
Notation "'always' st" := (VModuleCommonItemAlways VAlways st)
                            (in custom verilog_module at level 98, st custom verilog_stmt at level 97).
Notation "'always_comb' st" := (VModuleCommonItemAlways VAlwaysComb st)
                                 (in custom verilog_module at level 98, st custom verilog_stmt at level 97).
Notation "'always_latch' st" := (VModuleCommonItemAlways VAlwaysLatch st)
                                  (in custom verilog_module at level 98, st custom verilog_stmt at level 97).
Notation "'always_ff' st" := (VModuleCommonItemAlways VAlwaysFF st)
                               (in custom verilog_module at level 98, st custom verilog_stmt at level 97).

Notation "i is" := (VModuleItemsCons i is) (in custom verilog_module at level 99, right associativity).

Notation "mid iid '(' pcs ')' ;" :=
  (VModuleInsOne mid VParamValueAssignsNil (VHierInsOne iid pcs))
    (in custom verilog_module at level 98,
        mid custom verilog_expr at level 50, (* NOTE: the level must be smaller than any levels used in verilog_expr. *)
        iid custom verilog_expr at level 50, (* NOTE: the level must be smaller than any levels used in verilog_expr. *)
        pcs custom verilog_portconn at level 97).

Notation "'generate' gmi 'endgenerate'" := (VGeneratedModuleInsO gmi)
                                             (in custom verilog_module at level 99,
                                                 gmi custom verilog_gen at level 99).

Notation "'assert' 'property' ( pe ) ;" :=
  (VAssertProp (VPropSpecO None pe) None) (in custom verilog_module at level 98, pe custom verilog_pexpr at level 97).
Notation "'assume' 'property' ( pe ) ;" :=
  (VAssumeProp (VPropSpecO None pe)) (in custom verilog_module at level 98, pe custom verilog_pexpr at level 97).
Notation "'cover' 'property' ( pe ) ;" :=
  (VCoverProp (VPropSpecO None pe) None) (in custom verilog_module at level 98, pe custom verilog_pexpr at level 97).

Notation "'module' name '()' ; items 'endmodule'" :=
  (VModuleDeclAnsi name VParamPortsNil VAnsiPortDeclNil items)
    (in custom verilog_top at level 100, items custom verilog_module at level 99).
(** NOTE: interestingly ( ) cannot cover () *)
Notation "'module' name ( ) ; items 'endmodule'" :=
  (VModuleDeclAnsi name VParamPortsNil VAnsiPortDeclNil items)
    (in custom verilog_top at level 100, items custom verilog_module at level 99).
Notation "'module' name '(' ports ')' ; items 'endmodule'" :=
  (VModuleDeclAnsi name VParamPortsNil ports items)
    (in custom verilog_top at level 100,
        ports custom verilog_ports at level 99, items custom verilog_module at level 99).

Notation "'module' name #( pds ) '()' ; items 'endmodule'" :=
  (VModuleDeclAnsi name pds VAnsiPortDeclNil items)
    (in custom verilog_top at level 100,
        pds custom verilog_paramports at level 99,
        items custom verilog_module at level 99).
Notation "'module' name #( pds ) ( ) ; items 'endmodule'" :=
  (VModuleDeclAnsi name pds VAnsiPortDeclNil items)
    (in custom verilog_top at level 100,
        pds custom verilog_paramports at level 99,
        items custom verilog_module at level 99).
Notation "'module' name #( pds ) '(' ports ')' ; items 'endmodule'" :=
  (VModuleDeclAnsi name pds ports items)
    (in custom verilog_top at level 100,
        pds custom verilog_paramports at level 99,
        ports custom verilog_ports at level 99,
        items custom verilog_module at level 99).

(*! Tester *)

Module Tester.

  Inductive VId :=
  | tester
  | net_a | net_b | net_c
  | param_a | param_b | param_c
  | module_a | module_ins_a
  | task_a | func_a.

  Notation "'tester'" := tester (in custom verilog_top).

  (** NOTE: a hack to solve that the notation starting with '.' does not work at all. *)

  Notation "'.net_a'" := net_a (in custom verilog_portconnid).
  Notation "'.net_b'" := net_b (in custom verilog_portconnid).
  Notation "'.net_c'" := net_c (in custom verilog_portconnid).
  Notation "'.param_a'" := param_a (in custom verilog_portconnid).
  Notation "'.param_b'" := param_b (in custom verilog_portconnid).
  Notation "'.param_c'" := param_c (in custom verilog_portconnid).
  Notation "'.module_a'" := module_a (in custom verilog_portconnid).
  Notation "'.module_ins_a'" := module_ins_a (in custom verilog_portconnid).

  Notation "'.net_a'" := net_a (in custom verilog_expr).
  Notation "'.net_b'" := net_b (in custom verilog_expr).
  Notation "'.net_c'" := net_c (in custom verilog_expr).
  Notation "'.param_a'" := param_a (in custom verilog_expr).
  Notation "'.param_b'" := param_b (in custom verilog_expr).
  Notation "'.param_c'" := param_c (in custom verilog_expr).
  Notation "'.module_a'" := module_a (in custom verilog_expr).
  Notation "'.module_ins_a'" := module_ins_a (in custom verilog_expr).

  Notation "'net_a'" := net_a (in custom verilog_expr).
  Notation "'net_b'" := net_b (in custom verilog_expr).
  Notation "'net_c'" := net_c (in custom verilog_expr).
  Notation "'param_a'" := param_a (in custom verilog_expr).
  Notation "'param_b'" := param_b (in custom verilog_expr).
  Notation "'param_c'" := param_c (in custom verilog_expr).
  Notation "'module_a'" := module_a (in custom verilog_expr).
  Notation "'module_ins_a'" := module_ins_a (in custom verilog_expr).
  Notation "'task_a'" := task_a (in custom verilog_expr).
  Notation "'func_a'" := func_a (in custom verilog_expr).

  Definition VExprIdVId := @VExprId VId.
  Coercion VExprIdVId: VId >-> VExpr.
  Definition VPortIdsOneVId := @VPortIdsOne VId.
  Coercion VPortIdsOneVId: VId >-> VPortIds.

Definition tester0: @VModuleDecl VId := verilog_top:(
module tester
 #(parameter [0:0] param_a = 4'b0010,
   parameter param_c = 3
  )
  (net_a,
   input net_a,
   input wire net_b,
   input reg net_b,
   input [1:0] net_c,
   input wire [1:0] net_c,
   input reg [1:0] net_c,
   output net_c,
   output wire net_b,
   output reg net_b,
   output [1:0][1:0] net_b,
   output wire [31:0] net_a,
   output reg [31:0] net_a);
  module_a module_ins_a (.*, .net_a, .net_a(), .net_a(net_a), .*);
endmodule).

Definition tester1: @VModuleDecl VId := verilog_top:(
module tester ();
  module_a module_ins_a (.*, .net_a, .net_a(), .net_a(net_a), .*);
  parameter param_a = '0;
  parameter param_a = 4'('1)+param_b '('0); (* no way to allow `param_b'` (without whitespaces) *)
  parameter param_a = 4'b0101, param_b = 'd123, param_c = 9'o123;
  parameter param_a = 4567;
  parameter param_a = 16'h0xabc; (* workaround *)
  localparam param_a = 3'b111;
  localparam [param_c+3:0] param_a = 3'b111;
  localparam integer param_a = 10;
  input net_a; input reg net_a; input wire net_b; input [1:0] net_c;
  output net_a; output reg net_a; output wire net_b; output [1:0] net_c;
  input wire [31:1][31:0] net_c;
  output wire [31:1][31:0][1:0] net_c;
  bit net_a; bit net_a, net_b; bit [1:0] net_a; bit [1:0] net_a, net_b;
  logic net_a; logic net_a, net_b; logic [1:0] net_a; logic [1:0] net_a, net_b;
  reg net_a; reg net_a, net_b; reg [1:0] net_a; reg [1:0] net_a, net_b;
  wire net_a; wire net_a, net_b; wire [1:0] net_a; wire [1:0] net_a, net_b;
  wire net_a = 1'b1; wire net_b = param_c;
  wire net_a = param_c[param_a];
  integer param_a;
endmodule).

Definition tester2: @VModuleDecl VId := verilog_top:(
module tester ();
  assign net_a = 1'b0;
  assign net_b = (1+2'b1)-3*4/5;
  assign net_c = 1+-!~&|~&~|^^~~^2;
  logic param_b;
  assign net_c = net_a[param_a];
  assign net_c = param_a ? (param_b + 1) : param_c + 1;
  assign net_a = |{};
  assign net_a = &{1'b1};
  assign net_a = {1'b0, 1'b1};
  assign net_a = |{net_a-1, 'b1, 1'b1, 1+2/5};
  assign net_a = {net_b, net_c};
  assign net_b = {16{1'b1}};
  assign net_b = {net_a-1{net_b, 1'b1, 16}};
  assign net_b = {net_a-1{net_b, 1'b1, 16}};
  assign net_c = net_a[1'b1][1+2];
  assign net_c = net_a[0][net_b][2][31:0] inside {$signed(param_a), $unsigned(param_b + 1), param_c + 2};
  assign net_c = net_a[1'b1][1+2].net_b inside {2'b00, 2'b11};
endmodule).

Definition tester3: @VModuleDecl VId := verilog_top:(
module tester ();
  initial
    net_a = net_b;
  always_comb
    net_a = net_b;
  always_ff @(posedge net_a) begin
    net_a <= net_c;
    net_a <= (net_b <= net_c);
    net_a <= net_b <= net_c;
    net_b = net_c;
  end
  assign net_c = 1'b0;
  always_ff @(negedge net_a) begin
    net_a <= net_c;
  end
  always_ff @* begin
    forever net_a = net_b;
    repeat (1'b1) net_a = net_b;
  end
  always @* begin
    while (1'b1) net_b = net_c;
    do net_c = net_a; while (1'b0)
  end
  always begin
    for (param_a = 0; param_a < param_b; param_a = param_a + 1) begin
      net_a = net_b;
    end
    for (param_a = 0; param_a < param_b; param_a++) begin
      net_a = net_b;
    end
  end
  always begin
    if (net_a) net_b = 1'b1; else begin end
  end
  always begin
    case (net_a)
      param_a: case (net_b)
                 param_a: net_a[param_b] <= param_a;
                 default: begin end
               endcase
      (* param_b, param_c: net_b <= param_b; *)
      param_b: net_b <= param_b;
      default: net_c <= param_c;
    endcase
  end
endmodule).

Definition tester4: @VModuleDecl VId := verilog_top:(
module tester ();
  task task_a;
    begin end
  endtask
  function [1:0] func_a (input [1:0] net_a);
    return net_a;
  endfunction
  assign net_b = func_a(net_a);
  generate if (net_a)
    always begin
      net_a = func_a (param_a);
      net_b = func_a (param_a, param_b);
    end
  endgenerate
  generate if (net_a) begin
    assign net_a = param_a;
  end
  else if (net_b) begin
    assign net_b = param_b;
    assign net_c = param_c;
  end else
    always begin
      net_b = param_b;
    end
  endgenerate
endmodule).

Definition tester5: @VModuleDecl VId := verilog_top:(
module tester ();
  assert property (net_a == net_b);
  assume property (param_c);
  cover property (net_a |-> net_b);
  assert property (net_a |=> net_b |-> net_c);
  assert property (net_a or net_b and net_c |-> (net_a or net_b));
  assert property (net_a or (net_b and net_c) |-> net_a);
  assert property ((net_a or (net_b and net_c)) |-> net_a);
  assert property ((net_a |-> net_b) |=> net_c);
endmodule
).

End Tester.

