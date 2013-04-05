#ifndef INPUT_EXPRESSION_HPP__
#define INPUT_EXPRESSION_HPP__

class input_expression : public Named {
	char *mkName() const;
	input_expression(unsigned thread, unsigned vex_offset);
	input_expression(unsigned thread, const CfgLabel &);
	input_expression(unsigned thread, const CfgLabel &, const CfgLabel &);
	input_expression(const MemoryAccessIdentifier &before, const MemoryAccessIdentifier &after);
	void operator=(const input_expression &o); /* DNI */
public:
	enum inp_type {
		inp_entry_point,
		inp_control_flow,
		inp_register,
	};
	const inp_type tag;

	/* For all tags except inp_happens_before */
	const unsigned thread;
	/* Only for tag == inp_register */
	const unsigned vex_offset;
	/* Only for tag == inp_entry_point and tag == inp_control_flow */
	const CfgLabel label1;
	/* Only for tag == inp_control_flow */
	const CfgLabel label2;

	bool operator < (const input_expression &) const;
	bool operator ==(const input_expression &) const;
	bool operator !=(const input_expression &) const;
	bool matches(const IRExpr *) const;

	static std::pair<input_expression, bool> parse(const char *, const char **);

	input_expression()
		: tag((inp_type)-1),
		  thread(-1),
		  vex_offset(-1),
		  label1(CfgLabel::uninitialised()),
		  label2(CfgLabel::uninitialised())
	{}

	static input_expression registr(const IRExprGet *);
	static input_expression control_flow(const IRExprControlFlow *);
	static input_expression entry_point(const IRExprEntryPoint *);
};

#endif /* !INPUT_EXPRESSION_HPP__ */
