/**
 * Le contrôleur des entrées du clavier. Il réagit aussi à la souris pour
 * récupérer le focus.
 */

class LController extends JComponent implements KeyListener, MouseListener {
	// Le contrôleur garde une référence au labyrinthe.
	private LModel laby;

	// Constructeur : le contrôleur s'enregistre comme un récepteur des entrées
	// clavier et souris, et comme un élément graphique (nécessaire pour
	// récupérer le focus et les entrées).
	public LController(LModel laby, JFrame frame) {
		this.laby = laby;
		addKeyListener(this);
		addMouseListener(this);
		setFocusable(true);
		frame.add(this);
	}

	// Méthode qui récupère l'entrée clavier et appelle l'action correspondante
	// du héros. Si l'action du héros est valide, alors les monstres sont aussi
	// déplacés.
	public void keyTyped(KeyEvent e) {
		// À compléter.
	}
	// -- Fin de l'action du clavier.

	// Récupère le focus quand on clique dans la fenêtre graphique.
	public void mouseClicked(MouseEvent e) {
		requestFocusInWindow();
	}
	// Pas de réaction aux autres stimuli.
	public void keyPressed(KeyEvent e) {}
	public void keyReleased(KeyEvent e) {}
	public void mouseEntered(MouseEvent e) {}
	public void mouseExited(MouseEvent e) {}
	public void mousePressed(MouseEvent e) {}
	public void mouseReleased(MouseEvent e) {}
}
