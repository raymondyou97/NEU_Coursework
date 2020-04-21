package models;

import com.fasterxml.jackson.annotation.JsonIgnore;
import java.util.List;

import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.GenerationType;
import javax.persistence.Id;
import javax.persistence.ManyToOne;
import javax.persistence.OneToMany;
import javax.persistence.Table;

@Entity
@Table(name = "service_questions")
public class ServiceQuestion {
  @Id
  @GeneratedValue(strategy = GenerationType.IDENTITY)
  private Integer id;
  private String question;
  private String type;
  private String choices;
  @OneToMany(mappedBy = "serviceQuestion")
  @JsonIgnore
  private List<ServiceAnswer> serviceAnswers;
  @ManyToOne
  @JsonIgnore
  private Service service;

  public ServiceQuestion() {
  }

  public ServiceQuestion(String question, String type, String choices, List<ServiceAnswer> serviceAnswers,
      Service service) {
    this.question = question;
    this.type = type;
    this.choices = choices;
    this.serviceAnswers = serviceAnswers;
    this.service = service;
  }

  public Integer getId() {
    return id;
  }

  public void setId(Integer id) {
    this.id = id;
  }

  public String getQuestion() {
    return question;
  }

  public void setQuestion(String question) {
    this.question = question;
  }

  public String getType() {
    return type;
  }

  public void setType(String type) {
    this.type = type;
  }

  public String getChoices() {
    return choices;
  }

  public void setChoices(String choices) {
    this.choices = choices;
  }

  public Service getService() {
    return service;
  }

  public void setService(Service service) {
    this.service = service;
  }
}