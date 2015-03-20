/**
 *  Le labyrinthe proprement dit.
 */
import java.awt.*;
import java.awt.geom.*;
import java.awt.event.*;
import javax.swing.*;
import java.util.*;
class LModel extends Observable {
	// Un labyrinthe a : une hauteur, une largeur, un tableau de cellules,
	// un héros et une liste de monstres.
	private final int h, l;
	private Cell[][] laby;
	private Hero hero = null;
	private Arraylist<Monster> monsters;

	public Cell get(int i, int j) { return laby[i][j]; }
	public int  getH()            { return h; }
	public int  getL()            { return l; }

	// Construction d'un labyrinthe aux dimensions données.
	// À l'origine, il n'y a ni héros ni monstre, et toutes les cases
	// sont libres.
	public LModel(int h, int l) {
		this.h = h;
		this.l = l;
		this.laby = new Cell[h][l];
		for (int i = 0; i < h; i++)
		{
			for (int j = 0; j < l; j++)
			{
				laby[i][j] = new Cell(this, i, j);
			}
		}
		monsters = new Arraylist<Monster>;
	}

	// Méthode pour les déplacements du héros.
	// Déplacement d'une case dans une direction, puis notification de la vue.
	public void heroMove(Direction dir) {
		hero.move(dir);
		setChanged();
		notifyObservers();
	}

	// Méthodes pour la configuration du labyrinthe.
	public void putCell(int i, int j) {
		laby[i][j] = new Cell(this, i, j);
	}
	public void putWall(int i, int j) {
		laby[i][j] = new Wall(this, i, j);
	}
	public void putExit(int i, int j) {
		laby[i][j] = new Exit(this, i, j);
	}
	// public void putHero(int i, int j) {
	// 	if (this.hero == null) {
	// 	    hero = new Hero(laby[i][j]);
	// 	}
	// }
	// public void putMonster(int i, int j) {
	// 	monsters.add(new Monster(laby[i][j]));
	// }
	// public void putOpenDoor(int i, int j) {
	// 	laby[i][j] = Door.openDoorFactory(this, i, j);
	// }
	// public void putClosedDoor(int i, int j) {
	// 	laby[i][j] = Door.closedDoorFactory(this, i, j);
	// }
	// -- Fin des méthodes de configuration.
}
