package cs3500.music.view;

import javax.sound.midi.MidiUnavailableException;
import cs3500.music.model.Note;
import cs3500.music.model.IMusicModel;
import cs3500.music.model.Pitch;

public interface MusicView {

  /**
   * a factory class that renders the view for the user by taking a string as an input
   */
  class returnView {

    private IMusicModel<Note> model;

    public returnView(IMusicModel<Note> model) {
      this.model = model;
    }

    /**
     * returns corresponding view according to input
     * @param viewType represents the type of the view class the user wants to create
     * @return corresponding view
     * @throws MidiUnavailableException
     */
    public MusicView create(String viewType) throws MidiUnavailableException {
      if (viewType == "console") {
        return new ConsoleView(this.model);
      }
      else if (viewType == "midi") {
        return new MidiViewImpl(this.model);
      }
      else if (viewType == "gui") {
        return new GuiViewFrame(this.model);
      }
      else {
        throw new IllegalArgumentException(
                "Incorrect input");
      }
    }
  }

  /**
   * Allows the user to begin seeing the view, for GuiViewFrame
   */
  void initialize();

  /**
   * Displays the view to the user, for GuiViewFrame
   */
  void displayView();
}
