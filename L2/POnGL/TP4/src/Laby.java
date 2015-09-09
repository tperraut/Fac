import java.awt.*;
import java.awt.geom.*;
import java.awt.event.*;
import javax.swing.*;
import java.util.*;

/**
 *  Classe principale, initialisation du modèle, et mise en place du contrôleur
 *  et de la vue.
 */

public class Laby {

	public static void main(String[] args) {

		// Initialisation du schéma MVC.
		LModel laby = new LModel(10, 12);
		JFrame frame = new JFrame();
		LController controller = new LController(laby, frame);
		LView view = new LView(laby, frame);
		// -- Schéma MVC initialisé.

		// Configuration de la fenêtre graphique.
		frame.setTitle("Laby");
		frame.pack();
		frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		frame.setVisible(true);
		// -- Fenêtre graphique configurée.

		// Configuration du labyrinthe.
		// // Première section de configuration.
		for (int i=0; i<10; i++) {
			laby.putWall(i, 0);
			laby.putWall(i, 11);
		}
		for (int j=0; j<12; j++) {
			laby.putWall(0, j);
			laby.putWall(9, j);
		}
		for (int i=0; i<7; i++) {
			laby.putWall(i, 4);
		}
		for (int i=8; i<10; i++) {
			laby.putWall(i, 4);
		}
		for (int j=4; j<7; j++) {
			laby.putWall(3, j);
		}
		for (int j=8; j<12; j++) {
			laby.putWall(3, j);
		}
		laby.putExit(0, 1);
		// // -- Fin de la première section.
		// // Deuxième section de configuration.
		// laby.putHero(1,6);
		// // -- Fin de la deuxième section.
		// // Troisième section de configuration.
		// laby.putMonster(6, 8);
		// laby.putMonster(4, 2);
		// // -- Fin de la troisième section.
		// // Quatrième section de configuration.
		// laby.putOpenDoor(3, 7);
		// laby.putClosedDoor(7, 4);
		// // -- Fin de la quatrième section.
		// -- Labyrinthe configuré.
	}
}
