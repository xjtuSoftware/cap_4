#ifndef LIB_CORE_FILTERSYMBOLICEXPR_H_
#define LIB_CORE_FILTERSYMBOLICEXPR_H_

#include <set>
#include <string>
#include <vector>

#include "klee/Expr.h"
#include "klee/util/Ref.h"
#include "Trace.h"

namespace klee {

class FilterSymbolicExpr {

	private:
		std::set<std::string> allRelatedSymbolicExpr;

	public:
		void fillterTrace(Trace* trace, std::set<std::string> allRelatedSymbolicExpr);
		void filterUseless(Trace* trace);
		void filterUselessByTaint(Trace* trace);
		bool filterUselessWithSet(Trace* trace, std::set<std::string>* relatedSymbolicExpr);
		bool isRelated(std::string varName);
		static void addExprToSet(std::set<std::string>* Expr, std::set<std::string>* relatedSymbolicExpr);
		static void addExprToVector(std::vector<std::string>* Expr, std::vector<std::string>* relatedSymbolicExpr);
		static void addExprToVector(std::set<std::string>* Expr, std::vector<std::string>* relatedSymbolicExpr);
		static void resolveSymbolicExpr(ref<Expr> value, std::set<std::string>* relatedSymbolicExpr);
		static void resolveTaintExpr(ref<klee::Expr> value, std::vector<ref<klee::Expr> >* relatedSymbolicExpr,
				bool* isTaint);
		static std::string getVarName(ref<Expr> value);
		static std::string getVarName(std::string globalVarFullName);
		static std::string getFullName(ref<Expr> value);

};

}

#endif /* LIB_CORE_FILTERSYMBOLICEXPR_H_ */
