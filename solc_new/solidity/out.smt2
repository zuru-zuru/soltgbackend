Invariant generation in CHC encoding enabled!
relation registered: interface_0_SimpleStorage_33
relation registered: nondet_interface_1_SimpleStorage_33
relation registered: summary_constructor_2_SimpleStorage_33
relation registered: summary_3_function_get__32_33
relation registered: summary_4_function_get__32_33
relation registered: block_5_function_get__32_33
relation registered: block_6_get_31_33
relation registered: block_7_return_function_get__32_33
relation registered: block_8_while_header_get_22_33
relation registered: block_9_while_precondition_test_get_22_33
relation registered: block_10_while_body_get_21_33
relation registered: block_11_while_inductive_test_get_22_33
relation registered: block_12_get_31_33
Reached if block 
relation registered: invariant_target_0
UNSAT: Is an invariant
relation registered: invariant_target_1
UNSAT: Is an invariant
relation registered: invariant_target_2
SAT: Not an invariant
relation registered: invariant_target_3
relation registered: invariant_target_4
UNSAT: Is an invariant
UNSAT: Is an invariant
relation registered: block_13_function_get__32_33
relation registered: block_14_return_ghost_get_30_33
relation registered: block_15_function_get__32_33
relation registered: contract_initializer_16_SimpleStorage_33
relation registered: contract_initializer_entry_17_SimpleStorage_33
relation registered: contract_initializer_after_init_18_SimpleStorage_33
relation registered: implicit_constructor_entry_19_SimpleStorage_33
Reached if block 
No 
Warning: This is a pre-release compiler version, please do not use it in production.

Info: CHC: Requested query:
(set-logic HORN)
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-fun |interface_0_SimpleStorage_33| (Int |abi_type| |crypto_type| |state_type| Int) Bool)
(declare-fun |nondet_interface_1_SimpleStorage_33| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int) Bool)
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.prevrandao| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-fun |summary_constructor_2_SimpleStorage_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int) Bool)
(assert (forall( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (storedData_3_0 Int) (this_0 Int))
(=> (= error_0 0) (nondet_interface_1_SimpleStorage_33 error_0 this_0 abi_0 crypto_0 state_0 storedData_3_0 state_0 storedData_3_0)))
)
(declare-fun |summary_3_function_get__32_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int) Bool)
(declare-fun |summary_4_function_get__32_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int) Bool)
(assert (forall( (_6_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (storedData_3_2 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_SimpleStorage_33 error_0 this_0 abi_0 crypto_0 state_0 storedData_3_0 state_1 storedData_3_1) true) (and (= error_0 0) (summary_4_function_get__32_33 error_1 this_0 abi_0 crypto_0 tx_0 state_1 storedData_3_1 state_2 storedData_3_2 _6_1))) (nondet_interface_1_SimpleStorage_33 error_1 this_0 abi_0 crypto_0 state_0 storedData_3_0 state_2 storedData_3_2)))
)
(declare-fun |block_5_function_get__32_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int) Bool)
(declare-fun |block_6_get_31_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int) Bool)
(assert (forall( (_6_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (i_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(block_5_function_get__32_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1))
)
(assert (forall( (_6_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (i_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_5_function_get__32_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= storedData_3_1 storedData_3_0))) true) true)) true) (block_6_get_31_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1)))
)
(declare-fun |block_7_return_function_get__32_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int) Bool)
(declare-fun |block_8_while_header_get_22_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int) Bool)
(declare-fun |block_9_while_precondition_test_get_22_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int) Bool)
(declare-fun |block_10_while_body_get_21_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int) Bool)
(declare-fun |block_11_while_inductive_test_get_22_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int) Bool)
(declare-fun |block_12_get_31_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int) Bool)
(assert (forall( (_6_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_10_0 Int) (i_9_1 Int) (i_9_2 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_6_get_31_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1) (and (= i_9_2 expr_10_0) (and (=> true true) (and (= expr_10_0 0) (and (= _6_1 0) (and (= i_9_1 0) true)))))) true) (block_9_while_precondition_test_get_22_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_2)))
)
(assert (forall( (_6_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (i_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_8_while_header_get_22_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1) (and (= expr_14_1 (< expr_12_0 expr_13_0)) (and (=> true true) (and (= expr_13_0 10) (and (=> true (and (>= expr_12_0 0) (<= expr_12_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_12_0 i_9_1) true)))))) expr_14_1) (block_10_while_body_get_21_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1)))
)
(assert (forall( (_6_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (i_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_8_while_header_get_22_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1) (and (= expr_14_1 (< expr_12_0 expr_13_0)) (and (=> true true) (and (= expr_13_0 10) (and (=> true (and (>= expr_12_0 0) (<= expr_12_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_12_0 i_9_1) true)))))) (not expr_14_1)) (block_12_get_31_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1)))
)
(assert (forall( (_6_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_19_1 Int) (i_9_1 Int) (i_9_2 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_10_while_body_get_21_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1) (and (= i_9_2 expr_19_1) (and (=> true (and (>= expr_19_1 0) (<= expr_19_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_1 expr_18_1) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 i_9_1) (and (=> true (and (>= expr_18_1 0) (<= expr_18_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_18_1 (+ expr_16_0 expr_17_0)) (and (=> true true) (and (= expr_17_0 1) (and (=> true (and (>= expr_16_0 0) (<= expr_16_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_0 i_9_1) true)))))))))))) true) (block_11_while_inductive_test_get_22_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_2)))
)
(assert (forall( (_6_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (i_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_while_inductive_test_get_22_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1) true) true) (block_8_while_header_get_22_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1)))
)
(assert (forall( (_6_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (i_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_9_while_precondition_test_get_22_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1) true) true) (block_8_while_header_get_22_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1)))
)
(declare-fun |block_13_function_get__32_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int) Bool)
(assert (forall( (_6_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Bool) (i_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_get_31_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1) (and (= expr_26_1 (= expr_24_0 expr_25_0)) (and (=> true true) (and (= expr_25_0 10) (and (=> true (and (>= expr_24_0 0) (<= expr_24_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_0 i_9_1) true)))))) (and (and true (not expr_26_1)) (= error_1 1))) (block_13_function_get__32_33 error_1 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1)))
)
(assert (forall( (_6_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_1 Int) (i_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (block_13_function_get__32_33 error_1 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1) (summary_3_function_get__32_33 error_1 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1)))
)
(assert (forall( (_6_1 Int) (_6_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Bool) (expr_29_0 Int) (i_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_get_31_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1) (and (= _6_2 expr_29_0) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 i_9_1) (and (= error_1 error_0) (and (= expr_26_1 (= expr_24_0 expr_25_0)) (and (=> true true) (and (= expr_25_0 10) (and (=> true (and (>= expr_24_0 0) (<= expr_24_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_0 i_9_1) true)))))))))) true) (block_7_return_function_get__32_33 error_1 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_2 i_9_1)))
)
(declare-fun |block_14_return_ghost_get_30_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int) Bool)
(assert (forall( (_6_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Bool) (expr_29_0 Int) (i_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_14_return_ghost_get_30_33 error_1 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_2 i_9_1) (and (= _6_2 expr_29_0) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 i_9_1) (and (= error_1 error_0) (and (= expr_26_1 (= expr_24_0 expr_25_0)) (and (=> true true) (and (= expr_25_0 10) (and (=> true (and (>= expr_24_0 0) (<= expr_24_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_0 i_9_1) true)))))))))) true) (block_7_return_function_get__32_33 error_1 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_2 i_9_1)))
)
(assert (forall( (_6_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (i_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_return_function_get__32_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1) true) true) (summary_3_function_get__32_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1)))
)
(declare-fun |block_15_function_get__32_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int Int) Bool)
(assert (forall( (_6_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (i_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(block_15_function_get__32_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1))
)
(assert (forall( (_6_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (funds_2_0 Int) (i_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (storedData_3_2 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_15_function_get__32_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1 i_9_1) (and (summary_3_function_get__32_33 error_1 this_0 abi_0 crypto_0 tx_0 state_2 storedData_3_1 state_3 storedData_3_2 _6_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (> (|block.prevrandao| tx_0) 18446744073709551616) (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.prevrandao| tx_0) 0) (<= (|block.prevrandao| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 1833756220)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 109)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 76)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 230)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 60)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= storedData_3_1 storedData_3_0))) true) true))))))) true) (summary_4_function_get__32_33 error_1 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_3 storedData_3_2 _6_1)))
)
(assert (forall( (_6_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_SimpleStorage_33 this_0 abi_0 crypto_0 state_0 storedData_3_0) true) (and (summary_4_function_get__32_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1) (= error_0 0))) (interface_0_SimpleStorage_33 this_0 abi_0 crypto_0 state_1 storedData_3_1)))
)
(declare-fun |contract_initializer_16_SimpleStorage_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int) Bool)
(declare-fun |contract_initializer_entry_17_SimpleStorage_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int) Bool)
(assert (forall( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= storedData_3_1 storedData_3_0))) (contract_initializer_entry_17_SimpleStorage_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 storedData_3_0 storedData_3_1)))
)
(declare-fun |contract_initializer_after_init_18_SimpleStorage_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int) Bool)
(assert (forall( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_17_SimpleStorage_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 storedData_3_0 storedData_3_1) true) true) (contract_initializer_after_init_18_SimpleStorage_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 storedData_3_0 storedData_3_1)))
)
(assert (forall( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_18_SimpleStorage_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 storedData_3_0 storedData_3_1) true) true) (contract_initializer_16_SimpleStorage_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 storedData_3_0 storedData_3_1)))
)
(declare-fun |implicit_constructor_entry_19_SimpleStorage_33| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int) Bool)
(assert (forall( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= storedData_3_1 storedData_3_0))) (and true (= storedData_3_1 0))) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_19_SimpleStorage_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 storedData_3_0 storedData_3_1)))
)
(assert (forall( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (storedData_3_2 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_19_SimpleStorage_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 storedData_3_0 storedData_3_1) (and (contract_initializer_16_SimpleStorage_33 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 storedData_3_1 storedData_3_2) true)) (> error_1 0)) (summary_constructor_2_SimpleStorage_33 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 storedData_3_0 storedData_3_2)))
)
(assert (forall( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (storedData_3_2 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_19_SimpleStorage_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 storedData_3_0 storedData_3_1) (and (= error_1 0) (and (contract_initializer_16_SimpleStorage_33 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 storedData_3_1 storedData_3_2) true))) true) (summary_constructor_2_SimpleStorage_33 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 storedData_3_0 storedData_3_2)))
)
(assert (forall( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_SimpleStorage_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 storedData_3_0 storedData_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (> (|block.prevrandao| tx_0) 18446744073709551616) (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.prevrandao| tx_0) 0) (<= (|block.prevrandao| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_SimpleStorage_33 this_0 abi_0 crypto_0 state_1 storedData_3_1)))
)
(declare-fun |error_target_3| () Bool)
(assert (forall( (_6_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (storedData_3_0 Int) (storedData_3_1 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_SimpleStorage_33 this_0 abi_0 crypto_0 state_0 storedData_3_0) true) (and (summary_4_function_get__32_33 error_0 this_0 abi_0 crypto_0 tx_0 state_0 storedData_3_0 state_1 storedData_3_1 _6_1) (= error_0 1))) error_target_3))
)(assert
(forall ((UNUSED Bool))
(=> error_target_3 false)))
(check-sat)


Warning: CHC: 1 verification condition(s) could not be proved. Enable the model checker option "show unproved" to see all of them. Consider choosing a specific contract to be verified in order to reduce the solving problems. Consider increasing the timeout per query.

Warning: CHC analysis was not possible. No Horn solver was available. None of the installed solvers was enabled.

