package IG;

import javax.swing.JLabel;
import javax.swing.JComponent;

public class Texte extends JLabel {

    public Texte() {
	super("");
    }

    public Texte(String texte) {
	super(texte);
    }

    public void changeTexte(String texte) {
	this.setText(texte);
	this.repaint();
    }

}
