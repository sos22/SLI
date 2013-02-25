#ifndef STACKED_CDF_HPP__
#define STACKED_CDF_HPP__

namespace stackedCdf {

#define CdfKeys(iter)				\
	iter(Optimise)				\
	iter(Deadcode)				\
	iter(AvailExpressionBase)		\
	iter(AvailExpressionSSA)		\
	iter(LocalOptimise)			\
	iter(PhiElimination)			\
	iter(LoadElimination)			\
	iter(BuildCDG)				\
	iter(GetProbeCFGs)			\
	iter(CrashConstraint)			\
	iter(CrashConstraintResimplify)		\
	iter(CrashConstraintBuildCross)		\
	iter(CrashConstraintSymbolicExecute)	\
	iter(BuildWAtomic)			\
	iter(BuildWAtomicMachine)		\
	iter(BuildWAtomicResimplify)		\
	iter(BuildWAtomicSymbolicExecute)	\
	iter(DeriveRAtomic)			\
	iter(DeriveRAtomicResimplify)		\
	iter(DeriveRAtomicSymbolicExecute)	\
	iter(FindConflictingStores)		\
	iter(BuildStoreCFGs)			\
	iter(CompileStoreMachine)		\
	iter(StoreMachineInitialSimplify)	\
	iter(StoreInitialSimplify)		\
	iter(StoreConvertToSSA)			\
	iter(StoreSecondSimplify)		\
	iter(BuildProbeMachine)			\
	iter(CompileProbeMachine)		\
	iter(ProbeInitialSimplify)		\
	iter(ProbeConvertSSA)			\
	iter(ProbeSecondSimplify)		\
	iter(ProbeResimplify)			\
	iter(BDD)				\
	iter(root)

	enum stackedCdfBucket {
#define mk_item(name)				\
		cdf_ ## name ,
		CdfKeys(mk_item)
#undef mk_item
	};

#if CONFIG_STACKED_CDF
	void stacked_cdf_start(stackedCdfBucket);
	void stacked_cdf_stop(stackedCdfBucket);
	void start(void);
	void stop(bool);
#else
	static inline void stacked_cdf_start(stackedCdfBucket) {}
	static inline void stacked_cdf_stop(stackedCdfBucket) {}
	static inline void start(void) {}
	static inline void stop(bool) {}
#endif

#define mk_stubs(name)					\
	static inline void start ## name (void) {	\
		stacked_cdf_start(cdf_ ## name);	\
	}						\
	static inline void stop ## name (void) {	\
		stacked_cdf_stop(cdf_ ## name);		\
	}
	CdfKeys(mk_stubs)
#undef mk_stubs

};

#endif
