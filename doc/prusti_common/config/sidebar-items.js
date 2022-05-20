initSidebarItems({"fn":[["allow_unreachable_unsupported_code","When enabled, unsupported code is encoded as `assert false`. This way error messages are reported only for unsupported code that is actually reachable."],["assert_timeout","Maximum time (in milliseconds) for the verifier to spend on a single assertion. Set to `0` to disable timeout. Maps to the verifier command-line argument `--assertTimeout`."],["be_rustc","When enabled, Prusti will behave like `rustc`."],["cache_path","Path to a cache file, where verification cache will be loaded from and saved to. The default empty string disables saving any cache to disk. A path to a file which does not yet exist will result in using an empty cache, but then creating and saving to that location on exit."],["check_foldunfold_state","When enabled, additional, slow, checks for the `fold`/`unfold` algorithm will be generated."],["check_overflows","When enabled, binary operations and numeric casts will be checked for overflows."],["check_panics","When enabled, Prusti will check for an absence of `panic!`s."],["contracts_lib","Path to `libprusti_contracts*.rlib`."],["counterexample","When enabled, Prusti will try to find and print a counterexample for any failed assertion or specification."],["delete_basic_blocks","The given basic blocks will be replaced with `assume false`."],["disable_name_mangling","When enabled, Viper name mangling will be disabled."],["dump","Generate a dump of the settings"],["dump_borrowck_info","When enabled, borrow checking info will be output."],["dump_debug_info","When enabled, debug files will be created."],["dump_debug_info_during_fold","When enabled, the state of the fold-unfold algorithm after each step will be dumped to a file."],["dump_path_ctxt_in_debug_info","When enabled, branch context state will be output in debug files."],["dump_reborrowing_dag_in_debug_info","When enabled, reborrowing DAGs will be output in debug files."],["dump_viper_program","When enabled, the encoded Viper program will be output."],["enable_cache","When enabled, verification requests (to verify individual `fn`s) are cached to improve future verification. By default the cache is only saved in memory (of the `prusti-server` if enabled). For long-running verification projects use `CACHE_PATH` to save to disk."],["enable_ghost_constraints","When enabled, ghost constraints can be used in Prusti specifications."],["enable_purification_optimization","When enabled, impure methods are optimized using the purification optimization, which tries to convert heap operations to pure (snapshot- based) operations."],["enable_type_invariants","When enabled, type invariants can be declared on types using the `#[invariant(...)]` attribute."],["enable_verify_only_basic_block_path","When enabled, only the path given in `VERIFY_ONLY_BASIC_BLOCK_PATH` will be verified."],["encode_bitvectors","When enabled, bitwise integer operations are encoded using bitvectors."],["encode_unsigned_num_constraint","When enabled, non-negativity of unsigned integers will be encoded and checked."],["extra_jvm_args","Additional arguments to pass to the JVM when launching a verifier backend."],["extra_verifier_args","Additional arguments to pass to the verifier backend."],["foldunfold_state_filter","Filter for `fold`/`unfold` nodes when debug info is dumped."],["full_compilation","When enabled, compilation will continue and a binary will be generated after Prusti terminates."],["get_filtered_args","Return vector of arguments filtered out by prefix"],["hide_uuids","When enabled, UUIDs of expressions and specifications printed with `PRINT_TYPECKD_SPECS` are hidden."],["ignore_regions","When enabled, debug files dumped by `rustc` will not contain lifetime regions."],["intern_names","When enabled, Viper identifiers are interned to shorten them when possible."],["internal_errors_as_warnings","When enabled, internal errors are reported as warnings instead of errors. Used for testing."],["json_communication","When enabled, communication with the server will be encoded as JSON instead of the default bincode."],["log_dir","Path to directory in which log files and dumped output will be stored."],["max_log_file_name_length","Maximum allowed length of a log file name. If this is exceeded, the file name is truncated."],["no_verify","When enabled, verification is skipped altogether."],["no_verify_deps","When enabled, verification is skipped for dependencies."],["only_memory_safety","When enabled, only the core proof is verified."],["optimizations","Comma-separated list of optimizations to enable, or `\"all\"` to enable all. Possible values in the list are:"],["print_collected_verification_items","When enabled, prints the items collected for verification."],["print_desugared_specs","When enabled, prints the AST with desugared specifications."],["print_hash","When enabled, prints the hash of a verification request (the hash is used for caching). This is a debugging option which does not perform verification – it is similar to `NO_VERIFY`, except that this flag stops the verification process at a later stage."],["print_typeckd_specs","When enabled, prints the type-checked specifications."],["quiet","When enabled, user messages are not printed. Otherwise, message output into `stderr`."],["server_address","When set to an address and port (e.g. `\"127.0.0.1:2468\"`), Prusti will connect to the given server and use it for its verification backend."],["server_max_concurrency","Maximum amount of verification requests the server will work on concurrently. If not set, defaults to the number of (logical) cores on the system."],["server_max_stored_verifiers","Maximum amount of instantiated Viper verifiers the server will keep around for reuse. If not set, defaults to `SERVER_MAX_CONCURRENT_VERIFICATION_OPERATIONS`. It also doesn’t make much sense to set this option to less than that, since then the server will likely have to keep creating new verifiers, reducing the performance gained from reuse."],["simplify_encoding","When enabled, the encoded program is simplified before it is passed to the Viper backend."],["skip_unsupported_features","When enabled, features not supported by Prusti will be reported as warnings rather than errors."],["unsafe_core_proof","When enabled, the new core proof is used, suitable for unsafe code"],["use_more_complete_exhale","When enabled, a more complete `exhale` version is used in the verifier. See `consolidate`. Equivalent to the verifier command-line argument `--enableMoreCompleteExhale`."],["use_new_encoder","When enabled, Prusti uses the new VIR encoder."],["verification_deadline","Deadline (in seconds) within which Prusti should encode and verify the program."],["verify_only_basic_block_path","Verify only the single execution path goes through the given basic blocks. All basic blocks not on this execution path are replaced with `assume false`. Must be enabled using the `ENABLE_VERIFY_ONLY_BASIC_BLOCK_PATH` flag."],["verify_only_preamble","When enabled, only the preamble will be verified: domains, functions, and predicates."],["viper_backend","Verification backend to use. Possible values:"]],"mod":[["commandline",""]],"struct":[["Optimizations",""]]});