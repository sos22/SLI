#ifndef OFFLINE_ANALYSIS_HPP__
#define OFFLINE_ANALYSIS_HPP__

#define CRASHING_THREAD 73
#define STORING_THREAD 97

class CrashReason;

CrashReason *backtrackOneStatement(CrashReason *cr, IRStmt *stmt);

#endif /* !OFFLINE_ANALYSIS_HPP__ */
