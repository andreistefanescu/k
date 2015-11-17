package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
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
    private static final String MAP_EMPTY = "StackMemoryMap.empty";
    private static final String MAP_ADD = "StackMemoryMap.add";
    private static final String MAP_REMOVE = "StackMemoryMap.remove";
    private static final String MAP_FIND = "StackMemoryMap.find";

    public static Variable init(StringToken name, StringToken sort, TermContext context) {
        reset = true;
        return new Variable(name.stringValue(), Sort.of(sort.stringValue()));
    }

    public static StringToken gen(Term state, Term expression, TermContext context) {
        try {
            String result = "let stackMemory = !stackMemoryRef in ";

            String constraintString = "";
            for (Equality equality : constraint.equalities()) {
                if (DataStructures.isLookup(equality.leftHandSide())) {
                    // TODO: fix order of lookups
                    constraintString = "match " + toOCaml(equality.leftHandSide()) + " with " +  toOCaml(equality.rightHandSide()) + " -> " + constraintString;
                } else {
                    constraintString = constraintString + "if " + toOCaml(equality.leftHandSide()) + " <> " + toOCaml(equality.rightHandSide()) + " then raise Side_Condition_Failure; ";
                }
            }
            result = result + constraintString;

            result = result + "stackMemoryRef := " + toOCaml(state);

            if (!expression.equals(KSequence.EMPTY)) {
                result = result + "; " + toOCaml(expression);
            }

            return StringToken.of("(" + result + ")");
        } catch (AssertionError | ClassCastException e) {
            return StringToken.of("#error(" + state + "; " + expression + ")");
        }
    }

    public static StringToken name(Variable variable, TermContext context) {
        return StringToken.of(variable.name());
    }

    private static String toOCaml(Term term) {
        return ((SMTLibTerm) term.accept(new KILtoOCaml())).expression();
    }

    private static class KILtoOCaml extends CopyOnWriteTransformer {

        public final ImmutableMap<String, String> infix = ImmutableMap.<String, String>builder()
                .put("'_+Int_", "+")
                .put("'_-Int_", "-")
                .put("'_*Int_", "*")
                .put("'_/Int_", "/")
                .put("'_<Int_", "<")
                .put("'_<=Int_", "<=")
                .put("'_>Int_", ">")
                .put("'_>=Int_", ">=")
                .put("'_andBool_", "&&")
                .put("'_orBool_", "||")
                .put("'_==K_", "=")
                .put("'_=/=K_", "<>")
                .put("'_==Int_", "=")
                .build();
        public final ImmutableMap<String, String> prefix = ImmutableMap.<String, String>builder()
                .put("'notBool_", "not")
                .put("'ite", "ite")
                .put("Map:lookup", MAP_FIND)
                .build();
        public final ImmutableMap<String, String> constructors = ImmutableMap.<String, String>builder()
                .put("'object(_)", "C_pointer_object")
                .put("'null", "C_pointer_null")
                .put("'int", "C_type_int")
                .put("'double", "C_type_double")
                .put("'_*", "C_type_pointer")
                .put("'struct_", "C_type_struct")
                .put("'tv(_,_)", "C_typed_value")
                .put("'undef", "C_value_undef")
                .build();

        @Override
        public ASTNode transform(BoolToken boolToken) {
            return new SMTLibTerm(Boolean.toString(boolToken.booleanValue()));
        }

        @Override
        public SMTLibTerm transform(IntToken intToken) {
            return new SMTLibTerm(intToken.bigIntegerValue().toString());
        }

        @Override
        public SMTLibTerm transform(UninterpretedToken uninterpretedToken) {
            if (uninterpretedToken.sort().equals(Sort.of("Id"))) {
                return new SMTLibTerm("\"" + uninterpretedToken.value() + "\"");
            } else {
                throw new AssertionError();
            }
        }

        @Override
        public SMTLibTerm transform(Token token) {
            throw new UnsupportedOperationException();
        }

        @Override
        public SMTLibTerm transform(Variable variable) {
            return new SMTLibTerm(variable.name());
        }

        @Override
        public SMTLibTerm transform(KItem kItem) {
            if (!(kItem.kLabel() instanceof KLabelConstant)) {
                throw new AssertionError();
            }
            KLabelConstant kLabel = (KLabelConstant) kItem.kLabel();

            if (!(kItem.kList() instanceof KList)) {
                throw new AssertionError();
            }
            KList kList = (KList) kItem.kList();

            if (kList.hasFrame()) {
                throw new AssertionError();
            }

            if (kLabel.label().equals("'call")) {
                return new SMTLibTerm("(" + ((UninterpretedToken) kList.get(0)).value() + " " + ")");
            } else if (kLabel.label().equals("'return")) {
                return new SMTLibTerm("(raise Return(" + ((SMTLibTerm) kList.get(0).accept(this)).expression() + "))");
            } else if (kLabel.label().equals(DataStructures.MAP_UPDATE)) {
                return new SMTLibTerm("(" + MAP_ADD + " "
                        + ((SMTLibTerm) ((BuiltinMap) kList.get(1)).getEntries().entrySet().iterator().next().getKey().accept(this)).expression()
                        + " "
                        + ((SMTLibTerm) ((BuiltinMap) kList.get(1)).getEntries().entrySet().iterator().next().getValue().accept(this)).expression()
                        + " "
                        + ((SMTLibTerm) kList.get(0).accept(this)).expression() + ")");
            } else if (kLabel.label().equals(DataStructures.MAP_REMOVE_ALL)) {
                return new SMTLibTerm("(" + MAP_REMOVE + " "
                        + ((SMTLibTerm) ((BuiltinSet) kList.get(1)).elements().iterator().next().accept(this)).expression()
                        + " "
                        + ((SMTLibTerm) kList.get(0).accept(this)).expression() + ")");
            } else {
                List<String> arguments = kList.getContents().stream()
                        .map(t -> ((SMTLibTerm) t.accept(this)).expression())
                        .collect(Collectors.toList());

                if (infix.containsKey(kLabel.label())) {
                    assert arguments.size() == 2;
                    return new SMTLibTerm("(" + arguments.get(0) + " " + infix.get(kLabel.label()) + " " + arguments.get(1) + ")");
                } else if (prefix.containsKey(kLabel.label())) {
                    if (kLabel.label().equals(DataStructures.MAP_LOOKUP)) {
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
                } else if (constructors.containsKey(kLabel.label())) {
                    StringBuilder sb = new StringBuilder();
                    sb.append("(");
                    sb.append(constructors.get(kLabel.label()));
                    if (!arguments.isEmpty()) {
                        sb.append(" (");
                        sb.append(arguments.stream().reduce(((s1, s2) -> s1 + ", " + s2)).get());
                        sb.append(")");
                    }
                    sb.append(")");
                    return new SMTLibTerm(sb.toString());
                } else {
                    throw new AssertionError();
                }

            }
        }

        @Override
        public SMTLibTerm transform(BuiltinMap builtinMap) {
            if (!builtinMap.isConcreteCollection() && !builtinMap.hasFrame()) {
                throw new AssertionError();
            }

            String result = builtinMap.hasFrame() ? transform(builtinMap.frame()).expression() : MAP_EMPTY;
            for (Map.Entry<Term, Term> entry : builtinMap.getEntries().entrySet()) {
                result = "(" + MAP_ADD + " "
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
