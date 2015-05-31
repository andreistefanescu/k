// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;


public class FlattenCells extends CopyOnWriteTransformer {

    private final ConfigurationStructureMap config;

    public FlattenCells(Context context) {
        super("Flatten Cells", context);
        config = context.getConfigurationStructureMap();
    }

    @Override
    public ASTNode visit(Configuration node, Void _void)  {
        return node;
    }

    @Override
    public ASTNode visit(Cell node, Void _void)  {
        node = (Cell) super.visit(node, _void);
        if (node.getEllipses() == Cell.Ellipses.NONE
                || !config.get(node).hasChildren()
                || config.get(node).isStarOrPlusWrapper()) {
            return node;
        }

        List<Term> contents = node.getCellTerms();
        Set<String> labels = contents.stream()
                .map(Cell.class::cast)
                .map(Cell::getLabel)
                .collect(Collectors.toSet());
        Sets.SetView<String> missingCellLabels = Sets.difference(
                config.get(node).sons.keySet(),
                labels);

        List<Term> fullContents = Lists.newArrayList(contents);
        missingCellLabels.stream().forEach(l -> fullContents.add(completeCell(l)));

        Cell transformerNode = node.shallowCopy();
        transformerNode.setContents(new Bag(fullContents));
        transformerNode.setEllipses(Cell.Ellipses.NONE);
        return transformerNode;
    }

    private Cell completeCell(String label) {
        Cell cell = new Cell();
        cell.setLabel(label);
        cell.setEllipses(Cell.Ellipses.NONE);

        Term contents;
        if (!config.get(label).hasChildren() || config.get(label).isStarOrPlusWrapper()) {
            contents = Variable.getAnonVar(context.getCellSort(config.get(label).cell));
        } else {
            contents = new Bag(config.get(label).sons.keySet().stream()
                    .map(this::completeCell)
                    .collect(Collectors.toList()));
        }

        cell.setContents(contents);
        return cell;
    }

}
