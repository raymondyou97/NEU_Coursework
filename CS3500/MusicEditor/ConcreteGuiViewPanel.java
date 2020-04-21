package cs3500.music.view;

import java.awt.*;
import java.util.List;
import javax.swing.*;
import cs3500.music.model.IMusicModel;
import cs3500.music.model.Note;
import cs3500.music.model.Pitch;

/**
 * A dummy view that simply draws a string
 */
public class ConcreteGuiViewPanel extends JPanel {

  private IMusicModel<Note> model;

  ConcreteGuiViewPanel(IMusicModel<Note> model) {
    this.setSize((model.getHighestPitch() - model.getLowestPitch() + 10) * 10, 500);
    this.model = model;
    this.setLayout(new BoxLayout(this, BoxLayout.LINE_AXIS));

  }

  /**
   * draws all the parts of the music model
   * @param g
   */
  @Override
  public void paintComponent(Graphics g){
    // Handle the default painting
    super.paintComponent(g);

    //draws the grid
    for (int m = 0; m <= this.model.getDuration()/4 - 1; m += 1) {
      for (int p = 0; p <= this.model.getHighestPitch()-this.model.getLowestPitch(); p += 1) {
        g.drawRect(40 + m * 20 * 4, 20 + 5 + p * 20, 20 * 4, 20);
      }
    }

    // Draws the notes
    List<Note> notes = this.model.retrieveAllNotes();
    g.setColor(Color.green);

    for (Note n : notes) {
      g.fillRect(40 + n.getStartBeat() * 20, (this.model.getHighestPitch() - n.getPitchValue())
              * 20 + 26, (n.getEndBeat() - n.getStartBeat()) * 20, 19);
    }

    g.setColor(Color.BLACK);

    // Draws the black noteheads
    for (Note n : notes) {
      g.fillRect(40 + n.getStartBeat() * 20, (this.model.getHighestPitch() - n.getPitchValue())
              * 20 + 26, 20, 19);
    }

    // Prints beat numbers at the top
    for (int i = 0; i / 4 < model.getDuration(); i++) {
      if (i % 16 == 0) {
        g.drawString(Integer.toString(i), i * 20 + 40, 20);
      }
    }

    // Prints the notes on the left margin
    for (int i = this.model.getHighestPitch(); i >= this.model.getLowestPitch(); i--) {
      Pitch pitch1 = Pitch.findPitch(i % 12);

      int octaveValue = (int) Math.floor(i / 12);
      String pitchString = pitch1.toString() + String.valueOf(octaveValue);

      g.drawString(pitchString, 10, ((this.model.getHighestPitch() - i) * 20) + 40);
    }
  }

  /**
   * returns the preferred size
   * @return Dimension
   */
  @Override
  public Dimension getPreferredSize() {
    return new Dimension(this.model.getDuration() * 20 + 200,
            (this.model.getHighestPitch() - this.model.getLowestPitch()) * 20 + 200);
  }
}
