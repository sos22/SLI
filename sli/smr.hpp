#ifndef SMR_HPP__
#define SMR_HPP__

enum StateMachineRes { smr_crash, smr_survive, smr_unreached };
static inline const char *
nameSmr(StateMachineRes smr) {
	switch (smr) {
	case smr_crash: return "crash";
	case smr_survive: return "survive";
	case smr_unreached: return "unreached";
	}
	abort();
}
bool parseSmr(StateMachineRes *out, const char *str, const char **suffix);

#endif /* !SMR_HPP__ */