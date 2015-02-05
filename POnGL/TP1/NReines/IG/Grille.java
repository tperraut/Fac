package IG;

import javax.swing.JComponent;
import javax.swing.JPanel;
import java.awt.GridLayout;

public class Grille extends JPanel {

    public Grille (int hauteur, int largeur) {
	setLayout(new GridLayout(hauteur, largeur, 5, 5));
    }

    public void ajouteElement (JComponent element) {
	this.add(element);
    }

}
