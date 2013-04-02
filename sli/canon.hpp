#ifndef CANON_HPP__
#define CANON_HPP__

class OracleInterface;
class CrashSummary;
class AllowableOptimisations;

CrashSummary *optimise_crash_summary(VexPtr<CrashSummary, &ir_heap> cs,
				     const VexPtr<OracleInterface> &oracle,
				     GarbageCollectionToken token);
CrashSummary *canonicalise_crash_summary(VexPtr<CrashSummary, &ir_heap> input,
					 VexPtr<OracleInterface> oracle,
					 const AllowableOptimisations &optIn,
					 GarbageCollectionToken token);

#endif /* !CANON_HPP__ */
