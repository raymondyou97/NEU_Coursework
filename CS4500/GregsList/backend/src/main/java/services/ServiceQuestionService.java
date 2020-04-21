package services;

import models.ServiceAnswer;
import models.ServiceCategory;
import models.ServiceQuestion;
import repositories.PagedServiceQuestionRepository;
import repositories.ServiceAnswerRepository;
import repositories.ServiceQuestionRepository;
import utils.PaginationUtils;
import java.util.List;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.data.domain.Page;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.web.bind.annotation.DeleteMapping;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.PathVariable;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.PutMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RestController;

@RestController
@CrossOrigin(origins = "*")
public class ServiceQuestionService {
  @Autowired
  PagedServiceQuestionRepository pagedServiceQuestionRepository;
  @Autowired
  ServiceQuestionRepository serviceQuestionRepository;
  @Autowired
  ServiceAnswerRepository serviceAnswerRepository;

  @GetMapping("/api/serviceQuestions/paged")
  public Page<ServiceQuestion> findPagedServiceAnswers(@RequestParam(name = "page", required = false) Integer page,
      @RequestParam(name = "count", required = false) Integer count) {
    return pagedServiceQuestionRepository.findAll(PaginationUtils.getPageable(page, count));
  }

  @GetMapping("/api/serviceQuestions")
  public List<ServiceQuestion> findAllServiceQuestions() {
    return serviceQuestionRepository.getAllServiceQuestions();
  }

  @GetMapping("/api/serviceQuestions/{serviceQuestionId}")
  public ServiceQuestion findServiceQuestionById(@PathVariable("serviceQuestionId") Integer id) {
    return serviceQuestionRepository.findServiceQuestionById(id);
  }

  @PostMapping("/api/serviceQuestions")
  public ServiceQuestion createServiceQuestion(@RequestBody ServiceQuestion serviceQuestion) {
    return serviceQuestionRepository.save(serviceQuestion);
  }

  @PutMapping("/api/serviceQuestions/{serviceQuestionId}")
  public ServiceQuestion updateServiceQuestion(@PathVariable("serviceQuestionId") Integer id,
      @RequestBody ServiceQuestion serviceQuestionUpdates) {
    ServiceQuestion serviceQuestion = serviceQuestionRepository.findServiceQuestionById(id);
    serviceQuestion.setChoices(serviceQuestionUpdates.getChoices());
    serviceQuestion.setQuestion(serviceQuestionUpdates.getQuestion());
    serviceQuestion.setType(serviceQuestionUpdates.getType());
    return serviceQuestionRepository.save(serviceQuestion);
  }

  @DeleteMapping("/api/serviceQuestions/{serviceQuestionId}")
  public void deleteServiceQuestion(@PathVariable("serviceQuestionId") Integer id) {
    serviceQuestionRepository.deleteById(id);
  }

  @GetMapping("api/serviceQuestions/")
  public List<ServiceQuestion> findAllServiceQuestionsForType(
      @RequestParam(value = "serviceQuestionType") String type) {
    return serviceQuestionRepository.findAllServiceQuestionsForType(type);
  }

  @GetMapping("api/serviceQuestions/{serviceQuestionId}/service")
  public ServiceCategory findServiceForServiceQuestion(@PathVariable("serviceQuestionId") Integer id) {
    return serviceQuestionRepository.findServiceForServiceQuestion(id);
  }

  @GetMapping("api/serviceQuestions/{serviceQuestionId}/answers")
  public List<ServiceAnswer> findAllServiceAnswersForServiceQuestion(@PathVariable("serviceQuestionId") Integer id) {
    return serviceAnswerRepository.findAllServiceAnswersForServiceQuestion(id);
  }
}