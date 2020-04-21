package utils;

import models.ServiceAnswer;
import models.ServiceQuestion;

public class SearchPredicate {

  private ServiceQuestion serviceQuestion;
  private ServiceAnswer serviceAnswer;

  public SearchPredicate(ServiceQuestion serviceQuestion, ServiceAnswer serviceAnswer) {
    this.serviceQuestion = serviceQuestion;
    this.serviceAnswer = serviceAnswer;
  }

  public ServiceQuestion getServiceQuestion() {
    return serviceQuestion;
  }

  public void setServiceQuestion(ServiceQuestion serviceQuestion) {
    this.serviceQuestion = serviceQuestion;
  }

  public ServiceAnswer getServiceAnswer() {
    return serviceAnswer;
  }

  public void setServiceAnswer(ServiceAnswer serviceAnswer) {
    this.serviceAnswer = serviceAnswer;
  }

  public boolean match(SearchPredicate searchPredicate) {
    ServiceAnswer serviceAnswer1 = this.getServiceAnswer();
    ServiceQuestion serviceQuestion1 = this.getServiceQuestion();

    ServiceAnswer serviceAnswer2 = searchPredicate.getServiceAnswer();
    ServiceQuestion serviceQuestion2 = searchPredicate.getServiceQuestion();

    if (!(serviceQuestion1.getType().equals(serviceQuestion2.getType()))
        || !(serviceQuestion1.getChoices().equals(serviceQuestion2.getChoices()))
        || !(serviceQuestion1.getQuestion().equals(serviceQuestion2.getQuestion()))) {
      return false;
    }

    String type = serviceQuestion1.getType();

    if (type.equals("TrueFalse")) {
      return serviceAnswer1.getTrueFalseAnswer().equals(serviceAnswer2.getTrueFalseAnswer());
    }

    if (type.equals("MultipleChoice")) {
      return serviceAnswer1.getChoiceAnswer().equals(serviceAnswer2.getChoiceAnswer());
    }

    if (type.equals("Range")) {
      return serviceAnswer1.getMaxRangeAnswer() >= serviceAnswer2.getMinRangeAnswer()
          && serviceAnswer1.getMinRangeAnswer() <= serviceAnswer2.getMaxRangeAnswer();
    }

    return false;
  }
}
