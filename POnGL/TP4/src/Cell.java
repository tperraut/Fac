/**
 * Cases principales du labyrinthe.
 */

import java.awt.*;
import java.awt.geom.*;
import java.awt.event.*;
import javax.swing.*;
class Cell {
	// On maintient une référence vers le labyrinthe et les coordonnées.
	private final LModel laby;
	private final int i, j;
	private Creature HM;

	// Constructeur.
	public Cell(LModel laby, int i, int j) {
		this.laby = laby;
		this.i = i;
		this.j = j;
		setHM();
	}

	// Partie dessin.
	public void paintCell(Graphics2D g2d, int leftX, int topY, int scale) {
		Rectangle2D rect = new Rectangle2D.Double(leftX, topY, scale, scale);
		g2d.setPaint(setColor());
		g2d.fill(rect);
	}
	public Color setColor()
	{
		return (Color.WHITE);
	}
	public boolean addCreature (Creature c)
	{
		if (this.HM != null)
			return (false);
		this.HM = c;
		return (true)
	}
	public Creature setHM()
	{
		HM = null;
	}
}
