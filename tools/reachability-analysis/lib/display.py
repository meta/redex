# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

import enum
import html

from IPython.core.display import display, HTML


def phabricator_link(node):
    full_name, sep, _ = node.name.partition(";")
    if sep == "" or full_name[0] != "L":
        return None
    full_name = full_name[1:]  # Discard leading "L"
    return "https://phabricator.internmc.facebook.com/diffusion/FBS/browse/master/fbandroid/java/{}.java".format(
        full_name
    )


def render_node(node):
    """
    Create a HTML string representing a link. When clicked, it will execute
    code to display the details of :node.
    """
    name = html.escape(node.name)
    link = phabricator_link(node)
    if link is None:
        return "<pre>{}</pre>".format(name)
    return '<pre><a href="javascript:print_node(\'{0}\')">{0}</a> <a href="{1}">[phab]</a></pre>'.format(
        name, link
    )


def inject_scripts():
    script = """
        function print_node(node_name) {
            var kernel = Jupyter.notebook.kernel;
            var new_cell = Jupyter.notebook.insert_cell_below();
            new_cell.set_text("for node in graph.get_nodes('" + node_name + "'):\\n    display.display_node(node)");
            new_cell.execute();
        }
    """
    display(HTML("<script>{}</script>".format(script)))


def display_retainers(retainers):
    html = ["<p>"]
    for retaining_nodes, retained_nodes in list(retainers.items()):
        for node in retaining_nodes:
            html.append("{}".format(render_node(node)))
        html.append("<ul>")
        for node in retained_nodes:
            html.append("<li>{}</li>".format(render_node(node)))
        html.append("</ul>")
    html.append("</p>")
    display(HTML("".join(html)))


class NodeDisplayOptions(enum.Flag):
    PREDS = enum.auto()
    SUCCS = enum.auto()
    BOTH = PREDS | SUCCS


def display_node(node, option=NodeDisplayOptions.BOTH):
    html = [render_node(node)]
    if option & NodeDisplayOptions.PREDS:
        html.append("<br/>Predecessors:<br/>")
        html.append("<ul>")
        for pred in node.preds:
            html.append("<li>{}</li>".format(render_node(pred)))
        html.append("</ul>")
    if option & NodeDisplayOptions.SUCCS:
        html.append("<br/>Successors:<br/>")
        html.append("<ul>")
        for succ in node.succs:
            html.append("<li>{}</li>".format(render_node(succ)))
        html.append("</ul>")
    display(HTML("".join(html)))
