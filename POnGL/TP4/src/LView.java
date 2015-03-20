/**
 * La vue principale du labyrinthe, qui affiche l'ensemble de la structure
 * et ses occupants.
 */

class LView extends JComponent implements Observer {
	// La vue mémorise une référence au labyrinthe et à la fenêtre graphique.
	// On enregistre aussi la dimension et le côté de chaque case en pixels.
	private static final int SCALE = 40;
	private LModel laby;
	private JFrame frame;
	private Dimension dim;

	// Constructeur, où la vue s'enregistre comme un élément de la fenêtre
	// graphique et comme un observateur des modifications du labyrinthe.
	public LView(LModel laby, JFrame frame) {
		this.laby = laby;
		this.frame = frame;
		this.dim = new Dimension(SCALE*laby.getL(),SCALE*laby.getH());
		this.setPreferredSize(dim);
		laby.addObserver(this);
		frame.add(this);
	}

	// Méthode de mise à jour pour réagir aux modification du modèle. 
	public void update(Observable o, Object arg) {
		repaint();
	}

	// Méthode d'affichage du labyrinthe.
	public void paintComponent(Graphics g) {
		Graphics2D g2 = (Graphics2D)g;
		for (int i = 0; i < this.laby.getH(); i++)
		{
			for (int j = 0; j < this.laby.getL(); j++)
			{
				this.laby.get(i, j).paintCell(g2, j * SCALE, i * SCALE, SCALE);
			}
		}
	}
}
