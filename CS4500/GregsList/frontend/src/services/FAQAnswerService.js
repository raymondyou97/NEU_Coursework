import apiFetch, {
  postJson,
  deleteRequest,
  putRequest,
} from '../util/apiFetch';

export default class FAQAnswerService {
  static instance = null;
  
  static getInstance() {
    if (FAQAnswerService.instance === null) {
      FAQAnswerService.instance = new FAQAnswerService();
    }
    return this.instance;
  }

  findFAQAnswerById = id =>
    apiFetch(`/api/faas/${id}`).then(response => response.json());

  findAllFAQAnswers = () =>
    apiFetch('/api/faas').then(response => response.json());

  createFAQAnswer = (faqId, data) =>
    postJson(`/api/faqs/${faqId}/faas`, data).then(response => response.json());

  updateFAQAnswer = (id, data) =>
    putRequest(`/api/faas/${id}`, data).then(response => response.json());

  deleteFAQAnswer = id => deleteRequest(`/api/faas/${id}`);
}
