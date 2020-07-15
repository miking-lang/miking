from matplotlib.backends.backend_agg import FigureCanvasAgg
from matplotlib._pylab_helpers import Gcf
from ocaml import ocaml_show
from io import BytesIO

def show(close=None, block=None):
    """Show all figures as PNG payloads sent to the Jupyter frontend.

    Parameters
    ----------
    close : Not used.
    block : Not used.
    """
    for figure_manager in Gcf.get_all_fig_managers():
        fig = figure_manager.canvas.figure
        bytes_io = BytesIO()
        fig.canvas.print_figure(bytes_io, format='png', bbox_inches='tight')
        ocaml_show(bytes_io.getvalue())

FigureCanvas = FigureCanvasAgg
