package services;

import models.ServiceAnswer;
import models.ServiceQuestion;
import models.User;
import repositories.PagedServiceAnswerRepository;
import repositories.ServiceAnswerRepository;
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
public class ServiceAnswerService {
  @Autowired
  PagedServiceAnswerRepository pagedServiceAnswerRepository;
  @Autowired
  ServiceAnswerRepository serviceAnswerRepository;

  @GetMapping("/api/serviceAnswers/paged")
  public Page<ServiceAnswer> findPagedServiceAnswers(@RequestParam(name = "page", required = false) Integer page,
      @RequestParam(name = "count", required = false) Integer count) {
    return pagedServiceAnswerRepository.findAll(PaginationUtils.getPageable(page, count));
  }

  @GetMapping("/api/serviceAnswers")
  public List<ServiceAnswer> findAllServiceAnswers() {
    return serviceAnswerRepository.getAllServiceAnswers();
  }

  @GetMapping("/api/serviceAnswers/{serviceAnswerId}")
  public ServiceAnswer findServiceAnswerById(@PathVariable("serviceAnswerId") Integer id) {
    return serviceAnswerRepository.findServiceAnswerById(id);
  }

  @PostMapping("/api/serviceAnswers")
  public ServiceAnswer createServiceAnswer(@RequestBody ServiceAnswer serviceAnswer) {
    return serviceAnswerRepository.save(serviceAnswer);
  }

  @PutMapping("/api/serviceAnswers/{serviceAnswerId}")
  public ServiceAnswer updateServiceAnswer(@PathVariable("serviceAnswerId") Integer id,
      @RequestBody ServiceAnswer serviceAnswerUpdates) {
    ServiceAnswer serviceAnswer = serviceAnswerRepository.findServiceAnswerById(id);
    serviceAnswer.setChoiceAnswer(serviceAnswerUpdates.getChoiceAnswer());
    serviceAnswer.setMaxRangeAnswer(serviceAnswerUpdates.getMaxRangeAnswer());
    serviceAnswer.setMinRangeAnswer(serviceAnswerUpdates.getMinRangeAnswer());
    serviceAnswer.setTrueFalseAnswer(serviceAnswerUpdates.getTrueFalseAnswer());
    return serviceAnswerRepository.save(serviceAnswer);
  }

  @DeleteMapping("/api/serviceAnswers/{serviceAnswerId}")
  public void deleteServiceAnswer(@PathVariable("serviceAnswerId") Integer id) {
    serviceAnswerRepository.deleteById(id);
  }

  @GetMapping("api/serviceAnswers/")
  public List<ServiceAnswer> findAllServiceAnswersForProvider(
      @RequestParam(value = "serviceAnswerProviderId") Integer providerId) {
    return serviceAnswerRepository.findAllServiceAnswersForProvider(providerId);
  }

  @GetMapping("api/serviceAnswers/{serviceAnswerId}/question")
  public ServiceQuestion findServiceQuestionForServiceAnswer(@PathVariable("serviceAnswerId") Integer id) {
    return serviceAnswerRepository.findServiceQuestionForServiceAnswer(id);
  }

  @GetMapping("api/serviceAnswers/{serviceAnswerId}/provider")
  public User findProviderForServiceAnswer(@PathVariable("serviceAnswerId") Integer id) {
    return serviceAnswerRepository.findProviderForServiceAnswer(id);
  }
}