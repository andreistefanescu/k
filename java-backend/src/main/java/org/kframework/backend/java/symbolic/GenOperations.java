package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.DataStructures;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.SMTLibTerm;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.ASTNode;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import com.google.common.collect.ImmutableMap;


public class GenOperations {

    public static ConjunctiveFormula constraint;
    public static boolean reset;

    public static Variable init(StringToken name, StringToken sort, TermContext context) {
        reset = true;
        return new Variable(name.stringValue(), Sort.of(sort.stringValue()));
    }

    public static StringToken gen(Term state, Term expression, TermContext context) {
        String result = "let state = !stateRef in ";

        String constraintString = "";
        for (Equality equality : constraint.equalities()) {
            if (DataStructures.isLookup(equality.leftHandSide())) {
                // TODO: fix order of lookups
                constraintString = "let " + toOCaml(equality.rightHandSide()) + " = " + toOCaml(equality.leftHandSide()) + " in " + constraintString;
            } else {
                constraintString = constraintString + "if " + toOCaml(equality.leftHandSide()) + " <> " + toOCaml(equality.rightHandSide()) + " then raise Side_Condition_Failure; ";
            }
        }
        result = result + constraintString;

        result = result + "stateRef := " + toOCaml(state);

        if (!expression.equals(KSequence.EMPTY)) {
            result = result + "; " + toOCaml(expression);
        }

        return StringToken.of("(" + result + ")");
    }

    private static String toOCaml(Term term) {
        return ((SMTLibTerm) term.accept(new KILtoOCaml())).expression();
    }

    public static class KILtoOCaml extends CopyOnWriteTransformer {

        public final ImmutableMap<String, String> infix = ImmutableMap.<String, String>builder()
                .put("'_+Int_", "+")
                .put("'_/Int_", "/")
                .put("'_<=Int_", "<=")
                .put("'_andBool_", "&&")
                .put("'_orBool_", "||")
                .put("'_==K_", "=")
                .put("'_=/=K_", "<>")
                .put("'_==Int_", "=")
                .build();
        public final ImmutableMap<String, String> prefix = ImmutableMap.<String, String>builder()
                .put("'notBool_", "not")
                .put("Map:lookup", "ImpMap.find")
                .build();

        @Override
        public ASTNode transform(BoolToken boolToken) {
            return new SMTLibTerm(Boolean.toString(boolToken.booleanValue()));
        }

        @Override
        public ASTNode transform(IntToken intToken) {
            return new SMTLibTerm(intToken.bigIntegerValue().toString());
        }

        @Override
        public ASTNode transform(UninterpretedToken uninterpretedToken) {
            if (uninterpretedToken.sort().equals(Sort.of("Id"))) {
                return new SMTLibTerm("\"" + uninterpretedToken.value() + "\"");
            } else {
                throw new UnsupportedOperationException();
            }
        }

        @Override
        public ASTNode transform(Token token) {
            throw new UnsupportedOperationException();
        }

        @Override
        public ASTNode transform(Variable variable) {
            return new SMTLibTerm(variable.name());
        }

        @Override
        public ASTNode transform(KItem kItem) {
            if (!(kItem.kLabel() instanceof KLabelConstant)) {
                throw new UnsupportedOperationException();
            }
            KLabelConstant kLabel = (KLabelConstant) kItem.kLabel();

            if (!(kItem.kList() instanceof KList)) {
                throw new UnsupportedOperationException();
            }
            KList kList = (KList) kItem.kList();

            if (kList.hasFrame()) {
                throw new UnsupportedOperationException();
            }

            if (kLabel.label().equals("'updateMap")) {
                return new SMTLibTerm("(ImpMap.add "
                        + ((SMTLibTerm) ((BuiltinMap) kList.get(1)).getEntries().entrySet().iterator().next().getKey().accept(this)).expression()
                        + " "
                        + ((SMTLibTerm) ((BuiltinMap) kList.get(1)).getEntries().entrySet().iterator().next().getValue().accept(this)).expression()
                        + " "
                        + ((SMTLibTerm) kList.get(0).accept(this)).expression() + ")");
            } else {
                if (!infix.containsKey(kLabel.label()) && !prefix.containsKey(kLabel.label())) {
                    throw new UnsupportedOperationException();
                }

                List<String> arguments = kList.getContents().stream()
                        .map(t -> ((SMTLibTerm) t.accept(this)).expression())
                        .collect(Collectors.toList());

                if (infix.containsKey(kLabel.label())) {
                    if (arguments.size() != 2) {
                        throw new UnsupportedOperationException();
                    }
                    return new SMTLibTerm("(" + arguments.get(0) + " " + infix.get(kLabel.label()) + " " + arguments.get(1) + ")");
                } else {
                    if (kLabel.label().equals("Map:lookup")) {
                        if (arguments.size() != 2) {
                            throw new UnsupportedOperationException();
                        }
                        String temp = arguments.get(0);
                        arguments.set(0, arguments.get(1));
                        arguments.set(1, temp);
                    }
                    StringBuilder sb = new StringBuilder();
                    sb.append("(");
                    sb.append(prefix.get(kLabel.label()));
                    arguments.stream().forEach(s -> sb.append(" ").append(s));
                    sb.append(")");
                    return new SMTLibTerm(sb.toString());
                }
            }
        }

        @Override
        public ASTNode transform(BuiltinMap builtinMap) {
            if (!builtinMap.isConcreteCollection()) {
                throw new UnsupportedOperationException();
            }

            String result = "ImpMap.empty";
            for (Map.Entry<Term, Term> entry : builtinMap.getEntries().entrySet()) {
                result = "(ImpMap.add "
                        + ((SMTLibTerm) entry.getKey().accept(this)).expression()
                        + " "
                        + ((SMTLibTerm) entry.getValue().accept(this)).expression()
                        + " "
                        + result + ")";
            }

            return new SMTLibTerm(result);
        }
    }
}
