package org.kframework.backend.java.symbolic;

import com.google.common.collect.Sets;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.BuiltinList;
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

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;


public class GenOperations {

    public static ConjunctiveFormula constraint;
    public static boolean reset;
    private static final String MEMORY_MAP_EMPTY = "MemoryMap.empty";
    private static final String MEMORY_MAP_ADD = "MemoryMap.add";
    private static final String MEMORY_MAP_REMOVE = "MemoryMap.remove";
    private static final String MEMORY_MAP_FIND = "MemoryMap.find";
    private static final String MEMORY_MAP_SIZE = "MemoryMap.cardinal";
    private static final String OBJECT_MAP_EMPTY = "ObjectMap.empty";
    private static final String OBJECT_MAP_ADD = "ObjectMap.add";
    private static final String OBJECT_MAP_REMOVE = "ObjectMap.remove";
    private static final String OBJECT_MAP_FIND = "ObjectMap.find";
    private static final String OBJECT_MAP_SIZE = "ObjectMap.cardinal";

    public static Variable init(StringToken name, StringToken sort, TermContext context) {
        reset = true;
        return new Variable(name.stringValue(), Sort.of(sort.stringValue()));
    }

    public static StringToken gen(Term heapMemory, Term stackMemory, Term output, Term expression, TermContext context) {
        try {
            String result = "";

            String constraintString = "";
            Set<Variable> variables = Sets.newHashSet();
            for (Equality equality : constraint.equalities()) {
                if (DataStructures.isLookup(equality.leftHandSide())) {
                    // TODO: fix order of lookups
                    constraintString += "match " + toOCaml(equality.leftHandSide()) + " with " + toOCaml(equality.rightHandSide()) + " -> ";
                } else if (equality.leftHandSide() instanceof Variable
                        && !equality.rightHandSide().variableSet().contains((Variable) equality.leftHandSide())
                        && !variables.contains((Variable) equality.leftHandSide())) {
                    constraintString += "let " + toOCaml(equality.leftHandSide()) + " = " + toOCaml(equality.rightHandSide()) + " in ";
                } else {
                    constraintString += "if " + toOCaml(equality.leftHandSide()) + " <> " + toOCaml(equality.rightHandSide()) + " then raise Side_Condition_Failure; ";
                }
            }
            result += constraintString;

            result += "stackMemoryRef := " + toOCaml(stackMemory) + "; ";
            result += "heapMemoryRef := " + toOCaml(heapMemory);

            List<Term> formatItems = output instanceof BuiltinList ? ((BuiltinList) output).elements() : Collections.singletonList(output);
            for (Term formatItem : formatItems) {
                result += "; " + toOCaml(formatItem);
            }

            if (!expression.equals(KSequence.EMPTY)) {
                result += "; " + toOCaml(expression);
            }

            return StringToken.of(result);
        } catch (AssertionError | ClassCastException e) {
            return StringToken.of("#error(" + stackMemory + "; " + expression + ")");
        }
    }

    public static StringToken term(Term term, TermContext context) {
        return StringToken.of(toOCaml(term));
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
                .put("'fresh", "fresh")
                .put("'formatInt", "print_int")
                .put("'formatString", "print_string")
                .put("'sizeMap", OBJECT_MAP_SIZE)
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
        public SMTLibTerm transform(StringToken stringToken) {
            return new SMTLibTerm(stringToken.value());
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
            switch (variable.name()) {
            case "stackMemory":
            case "heapMemory":
                return new SMTLibTerm("!" + variable.name() + "Ref");
            default:
                return new SMTLibTerm(variable.name());
            }

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
                return new SMTLibTerm("(" + ((UninterpretedToken) kList.get(0)).value() + " " + flattenArgumentList((KItem) kList.get(1)).stream().map(t -> ((SMTLibTerm) t.accept(this)).expression()).collect(Collectors.joining(" ")) + ")");
            } else if (kLabel.label().equals("'return")) {
                if (kList.get(0).sort().equals(Sort.of("Value"))) {
                    return new SMTLibTerm("(raise (Return " + ((SMTLibTerm) kList.get(0).accept(this)).expression() + "))");
                } else {
                    return new SMTLibTerm("(raise (Return " + "(C_value_" + kList.get(0).sort().toString().toLowerCase() + " " + ((SMTLibTerm) kList.get(0).accept(this)).expression() + ")))");
                }
            } else if (kLabel.label().equals(DataStructures.MAP_LOOKUP)) {
                return new SMTLibTerm("(" + (kList.get(1).sort().name().equals("Pointer") ? MEMORY_MAP_FIND : OBJECT_MAP_FIND) + " "
                        + ((SMTLibTerm) kList.get(1).accept(this)).expression()
                        + " "
                        + ((SMTLibTerm) kList.get(0).accept(this)).expression() + ")");
            } else if (kLabel.label().equals(DataStructures.MAP_UPDATE)) {
                return new SMTLibTerm("(" + (((BuiltinMap) kList.get(1)).getEntries().entrySet().iterator().next().getKey().sort().name().equals("Pointer") ? MEMORY_MAP_ADD : OBJECT_MAP_ADD) + " "
                        + ((SMTLibTerm) ((BuiltinMap) kList.get(1)).getEntries().entrySet().iterator().next().getKey().accept(this)).expression()
                        + " "
                        + ((SMTLibTerm) ((BuiltinMap) kList.get(1)).getEntries().entrySet().iterator().next().getValue().accept(this)).expression()
                        + " "
                        + ((SMTLibTerm) kList.get(0).accept(this)).expression() + ")");
            } else if (kLabel.label().equals(DataStructures.MAP_REMOVE_ALL)) {
                return new SMTLibTerm("(" + (((BuiltinSet) kList.get(1)).elements().iterator().next().sort().name().equals("Pointer") ? MEMORY_MAP_REMOVE : OBJECT_MAP_REMOVE) + " "
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
                    StringBuilder sb = new StringBuilder();
                    sb.append("(");
                    sb.append(prefix.get(kLabel.label()));
                    arguments.stream().forEach(s -> sb.append(" ").append(s));
                    sb.append(")");
                    return new SMTLibTerm(sb.toString());
                } else if (constructors.containsKey(kLabel.label())) {
                    if (constructors.get(kLabel.label()).equals("C_typed_value") && !kList.get(1).sort().equals(Sort.of("Value"))) {
                        return new SMTLibTerm("(C_typed_value (" + arguments.get(0) + ", (C_value_" + kList.get(1).sort().toString().toLowerCase() + " " + arguments.get(1) + ")))");
                    }
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

        private List<Term> flattenArgumentList(KItem kItem) {
            if (kItem.klabel().name().equals("'_,_")) {
                return ImmutableList.<Term>builder()
                        .add((Term) kItem.klist().items().get(0))
                        .addAll(flattenArgumentList((KItem) kItem.klist().items().get(1)))
                        .build();
            } else if (kItem.klabel().name().equals("'.List{\"'_,_\"}")) {
                return ImmutableList.of();
            } else {
                throw new AssertionError();
            }
        }

        @Override
        public SMTLibTerm transform(BuiltinMap builtinMap) {
            assert builtinMap.isConcreteCollection() || builtinMap.hasFrame() && builtinMap.baseTerms().size() == 1;
            assert !builtinMap.isEmpty();

            String empty = null;
            String add = null;
            if (!builtinMap.getEntries().isEmpty()) {
                if (builtinMap.getEntries().keySet().iterator().next().sort().name().equals("Pointer")) {
                    empty = MEMORY_MAP_EMPTY;
                    add = MEMORY_MAP_ADD;
                } else {
                    empty = OBJECT_MAP_EMPTY;
                    add = OBJECT_MAP_ADD;
                }
            }

            String result = builtinMap.hasFrame() ? transform(builtinMap.frame()).expression() : empty;
            for (Map.Entry<Term, Term> entry : builtinMap.getEntries().entrySet()) {
                result = "(" + add + " "
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
